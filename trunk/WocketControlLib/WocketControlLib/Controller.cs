using System;
using System.Collections.Generic;
using System.Text;
using Winterdom.IO.FileMap;
using System.Runtime.InteropServices;
using System.IO;
using System.Diagnostics;

namespace WocketControlLib
{
    /// <summary>
    /// The Controller class mostly acts as the translator between WocketSensor
    /// and the FileMap library. WocketSensors don't know about MemoryMappedFiles 
    /// (MMFs), inter-process communication, etc. They only know that they ask the 
    /// Controller for a stream to write to and read from, or to tell them 
    /// whether or not they are responsible for calculating features or not. 
    /// <p>
    /// The Controller holds references to every MMF that this process uses,
    /// along with every stream that is opened on those MMFs. It communicates
    /// with Controllers in other processes to determine which process is
    /// "working" if two or more processes share a sensor. It handles re-allocating
    /// streams that are too small (although only when a WocketSensor tells it to).
    /// Finally, the Controller is responsible for shutting down resources when
    /// the process is ending. 
    /// <p>
    /// Note about garbage collection: The Controller uses GC.SuppressFinalize and
    /// GC.ReRegisterForFinalize liberally. This is necessary so that the 
    /// destructor for the Controller can signal the other processes before
    /// shutting down.
    /// </summary>
    public class Controller
    {

        #region constants
        private static string CONTROL_MUTEX_NAME = "WocketControllerMutex";
        private static string CONTROL_MAPPED_FILE_NAME = "WocketControllerMappedFile";
        private static int ERROR_ALREADY_EXISTS = 183;
        private static int ERROR_FILE_NOT_FOUND = 2;
        private static int DEFAULT_MAPPED_FILE_SIZE = 512;
        /*
        private static uint WAIT_ABANDONED = 0x80;
        private static uint WAIT_TIMEOUT = 0x00000102;
        */
        private static uint DEFAULT_WAIT_TIME = 1000;

        private static uint DELETE_PERMISSION = 0x00010000;
        private static uint SYNCHRONIZE_PERMISSION = 0x00100000;
        private static uint wocketPermissions = DELETE_PERMISSION | SYNCHRONIZE_PERMISSION;

        private static int DEFAULT_PROCESS_MAX = 100;//This is the max number of processes sharing the MMF. 100 is pretty high.

        private static int DEFAULT_IPC_MMF_SIZE = 1024;
        private const int DEFAULT_DATA_MMF_SIZE = 128;//0x4000;
        #endregion

        #region variables
        private static Controller instance = new Controller();
        private int processID = 0;
        //private int refcount = 0;
        //This memory mapped file is where the state of the controller is kept. Before you
        //write to it, you must acquire the controllermutex
        private MemoryMappedFile mmf = null;
        //the program actually reads/writes the MMF through this stream
        private Stream mmfStream = null;
        //These are wrappers that makes it easier to manipulate the mmfStream
        private BinaryWriter mmfWriter = null;
        private BinaryReader mmfReader = null;

        //this mutex controls all accesses to the MMF. You should not
        //hold this mutex for more than DEFAULT_WAIT_TIME
        private IntPtr controllerMutexHandle = IntPtr.Zero;


        //These are the streams that let different processes talk to each other
        //they're mostly used by OpenFeature() and FeatureStreams
        //invariant: If a key exists in ipcMutexes, then it also exists in the 
        //other ipc* dictionaries. Similarly, if a key does not exist in ipcMutexes,
        //it must also not exist in the other ipc* dictionaries. You should acquire
        //the appropriate ipcMutex before using any of the other ipc*
        private Dictionary<Type, MemoryMappedFile> ipcMmfs = new Dictionary<Type, MemoryMappedFile>();
        private Dictionary<Type, Stream> ipcStreams = new Dictionary<Type, Stream>();
        private Dictionary<Type, BinaryWriter> ipcWriters = new Dictionary<Type, BinaryWriter>();
        private Dictionary<Type, BinaryReader> ipcReaders = new Dictionary<Type, BinaryReader>();
        private Dictionary<Type, IntPtr> ipcMutexes = new Dictionary<Type, IntPtr>();
        private Dictionary<Type, MemoryMappedFile> openFeatureMmfs = new Dictionary<Type, MemoryMappedFile>();
        private Dictionary<Type, Stream> openFeatureStreams = new Dictionary<Type, Stream>();
        private Dictionary<Type, BinaryReader> openFeatureReaders = new Dictionary<Type, BinaryReader>();
        private Dictionary<Type, BinaryWriter> openFeatureWriters = new Dictionary<Type, BinaryWriter>();
        private Dictionary<Type, List<Feature>> thisProcessFeatures = new Dictionary<Type, List<Feature>>();
        private Dictionary<Type, Dictionary<Feature, MemoryMappedFile>> featureStreamMmfs = new Dictionary<Type, Dictionary<Feature, MemoryMappedFile>>();
        private Dictionary<Type, Dictionary<Feature, Stream>> featureWriterStreams = new Dictionary<Type, Dictionary<Feature, Stream>>();

        
        //controls whether the MMF has been initialized in this process
        private bool initialized = false;

        //controls whether or not debugging behavior is enabled
        //FIXME: take this out
        private bool debugging = true;

        //used as temporary storage when re-allocating streams
        private byte[] tempBuffer = new byte[DEFAULT_DATA_MMF_SIZE];
        #endregion


        private Controller() 
        {
            processID = Process.GetCurrentProcess().Id;
        }

        ~Controller()
        {
            if (controllerMutexHandle == IntPtr.Zero)
                throw new Exception("The controller mutex handle is uninitialized, this shouldn't happen");

            uint error = WaitForSingleObject(controllerMutexHandle, DEFAULT_WAIT_TIME);
            if (error != 0)
                throw new Exception("Coulnd't acquire the controller mutex");
            
            //make sure that all the other processes are notified if the 
            //working process is dying
            foreach (Type sensorType in ipcMutexes.Keys)
            {
                if (this.IsWorkingProcess(sensorType))
                    this.StopWorking(sensorType);
                GC.ReRegisterForFinalize(ipcMmfs[sensorType]);
                GC.ReRegisterForFinalize(ipcStreams[sensorType]);
                GC.ReRegisterForFinalize(ipcReaders[sensorType]);
                GC.ReRegisterForFinalize(ipcWriters[sensorType]);
                
                //remove all the local process features from the inter-process list of features
                List<Feature> featuresToRemove = new List<Feature>(thisProcessFeatures[sensorType]);
                foreach (Feature f in featuresToRemove)
                {
                    RemoveFeature(sensorType, f);
                }
                GC.ReRegisterForFinalize(openFeatureMmfs[sensorType]);
                GC.ReRegisterForFinalize(openFeatureStreams[sensorType]);
                GC.ReRegisterForFinalize(openFeatureReaders[sensorType]);
                GC.ReRegisterForFinalize(openFeatureWriters[sensorType]);
            }
            
            //now that all the sensors have stopped working
            //it's safe to finalize the various feature data streams
            foreach (Type type in featureStreamMmfs.Keys)
            {
                foreach (Feature f in featureStreamMmfs[type].Keys)
                {
                    GC.ReRegisterForFinalize(featureStreamMmfs[type][f]);
                    GC.ReRegisterForFinalize(featureWriterStreams[type][f]);
                }
                GC.ReRegisterForFinalize(featureStreamMmfs[type]);
                GC.ReRegisterForFinalize(featureWriterStreams[type]);
            }
            GC.ReRegisterForFinalize(featureStreamMmfs);
            GC.ReRegisterForFinalize(featureWriterStreams);

            mmfStream.Seek(1, SeekOrigin.Begin);
            byte numberOfProcesses = mmfReader.ReadByte();
            if (numberOfProcesses <= 1)//ok since byte is an unsigned type (0-256)
            {
                mmfWriter.Seek(0, SeekOrigin.Begin);
                for (int ii = 0; ii < DEFAULT_MAPPED_FILE_SIZE; ii++)
                {
                    mmfWriter.Write(Convert.ToByte(0));
                }
            }
            else
            {
                mmfWriter.Seek(1, SeekOrigin.Begin);
                mmfWriter.Write(numberOfProcesses - 1);
                int id;
                int index = 1;
                mmfReader.BaseStream.Seek(2, SeekOrigin.Begin);
                do
                {
                    id = mmfReader.ReadInt32();
                    index++;
                } while (id != this.processID && index <= DEFAULT_PROCESS_MAX);
                //shift all the IDs down one space
                id = mmfReader.ReadInt32();
                while (id != 0 && index <= DEFAULT_PROCESS_MAX) {   
                    mmfWriter.BaseStream.Seek(-2 * sizeof(int), SeekOrigin.Current);
                    mmfWriter.Write(id);
                    mmfReader.BaseStream.Seek(sizeof(int), SeekOrigin.Current);
                    id = mmfReader.ReadInt32();
                    index++;
                }
                if (index > DEFAULT_PROCESS_MAX)
                    throw new Exception("Overran the process index");
                //write over the last ID with zeros
                mmfWriter.BaseStream.Seek(-2 * sizeof(int), SeekOrigin.Current);
                mmfWriter.Write(id);
                //this is debugging info
                if (debugging)
                {
                    mmfStream.Seek(0, SeekOrigin.Begin);
                    byte[] localCopy = new byte[DEFAULT_MAPPED_FILE_SIZE];
                    for (int ii = 0; ii < DEFAULT_MAPPED_FILE_SIZE; ii++)
                    {
                        localCopy[ii] = mmfReader.ReadByte();
                    }
                    localCopy[0] += 1;//does nothing, just a break point
                }
            }
            //mmfWriter.Flush();
            mmfWriter.Close();
            mmfReader.Close();
            mmfStream.Close();
            mmf.Close();

            if (!ReleaseMutex(controllerMutexHandle))
                throw new Exception("Couldn't release the controller mutex");

            if (!CloseHandle(controllerMutexHandle))
                throw new Exception("Couldn't close the controller mutex handle");

            GC.ReRegisterForFinalize(mmf);
            GC.ReRegisterForFinalize(mmfStream);
            GC.ReRegisterForFinalize(mmfReader);
            GC.ReRegisterForFinalize(mmfWriter);
            GC.ReRegisterForFinalize(thisProcessFeatures);
            GC.ReRegisterForFinalize(openFeatureMmfs);
            GC.ReRegisterForFinalize(openFeatureStreams);
            GC.ReRegisterForFinalize(openFeatureReaders);
            GC.ReRegisterForFinalize(openFeatureWriters);
            GC.ReRegisterForFinalize(featureStreamMmfs);
            GC.ReRegisterForFinalize(featureWriterStreams);

            controllerMutexHandle = IntPtr.Zero;
        }

        /// <summary>
        /// Get the instance of Controller for this process. Controller is a Singleton,
        /// so only one instance ever exists for a single process.
        /// </summary>
        /// <returns></returns>
        public static Controller getInstance()
        {
            //open up the correct mapped file
            if (instance.controllerMutexHandle == IntPtr.Zero)
                instance.controllerMutexHandle = instance.getMutexHandle(CONTROL_MUTEX_NAME);
            //acquire the mutex
            uint error = WaitForSingleObject(instance.controllerMutexHandle, DEFAULT_WAIT_TIME);
            if (error != 0)
                throw new Exception("Couldn't acquire the controller mutex within the time limit");
            
            if (instance.initialized)
                return instance;

            //now open the MMF
            if (instance.mmf == null)
                instance.openMMF();
            instance.setupMMF();
            instance.initialized = true;

            GC.SuppressFinalize(instance.mmf);
            GC.SuppressFinalize(instance.mmfStream);
            GC.SuppressFinalize(instance.mmfReader);
            GC.SuppressFinalize(instance.mmfWriter);
            GC.SuppressFinalize(instance.thisProcessFeatures);
            GC.SuppressFinalize(instance.openFeatureMmfs);
            GC.SuppressFinalize(instance.openFeatureStreams);
            GC.SuppressFinalize(instance.openFeatureReaders);
            GC.SuppressFinalize(instance.openFeatureWriters);
            GC.SuppressFinalize(instance.featureStreamMmfs);
            GC.SuppressFinalize(instance.featureWriterStreams);
            
            if (!ReleaseMutex(instance.controllerMutexHandle))
                throw new Exception("Couldn't release the controller mutex");

            return instance;
        }

        /*
         * Set up the MMF by adding information for this process. Assumes
         * that the MMF mutex is acquired and that mmf, mmfStream,
         * mmfWriter, etc already exist.
         * 
         */
        private void setupMMF()
        {
            //a unique ID for this process
            int myProcessID = Process.GetCurrentProcess().Id;

            //FIXME: I think this is all unnecessary. The decision about
            //which process is working is handled by the openFeatureStreams.
            //The only reason to have this is if for some reason we need to know
            //about ALL other processes that are using WocketSensors, instead
            //of just ones that share a feature with us.

            //Check whether this is the first process
            mmfReader.BaseStream.Seek(0, SeekOrigin.Begin);
            byte firstByte = mmfReader.ReadByte();
            if (firstByte == 0)
            {
                mmfWriter.Seek(0, 0);
                mmfWriter.Write(Convert.ToByte(1));//first byte indicates whether the MMF is initialized or not
                mmfWriter.Write(Convert.ToByte(1));//second byte indicates how many processes are using the MMF
                mmfWriter.Write(myProcessID);//The next DEFAULT_PROCESS_MAX 32-bit ints are the unique process IDs

            }
            else
            {
                //Another process is already running 
                byte numberOfProcesses = mmfReader.ReadByte();
                mmfWriter.Seek(-1, SeekOrigin.Current);
                mmfWriter.Write(Convert.ToByte(numberOfProcesses + 1));//increment the number of processses
                mmfWriter.Seek(numberOfProcesses * sizeof(int), SeekOrigin.Current);
                mmfWriter.Write(myProcessID);
            }
            if (debugging)
            {
                byte[] localCopy = new byte[DEFAULT_MAPPED_FILE_SIZE];
                mmfStream.Seek(0, SeekOrigin.Begin);
                mmfStream.Read(localCopy, 0, localCopy.Length);
                localCopy[0] += 1;//does nothing, just a debug point.
            }
        }

        private void openMMF()
        {
            try
            {
                mmf = MemoryMappedFile.Create(null, MapProtection.PageReadWrite, DEFAULT_MAPPED_FILE_SIZE, CONTROL_MAPPED_FILE_NAME);
                mmfStream = mmf.MapView(MapAccess.FileMapWrite, 0, DEFAULT_MAPPED_FILE_SIZE);
                mmfReader = new BinaryReader(mmfStream);
                mmfWriter = new BinaryWriter(mmfStream);
            }
            catch (Exception exception)
            {
                throw new Exception("Couldn't open the memory-mapped file: " + exception);
            }
            
        }

        //safely create/open a mutex and return the handle, even in the presence
        //of other processes trying to create/open the same mutex
        private IntPtr getMutexHandle(string mutexName)
        {
            IntPtr mutexHandle = CreateMutex(IntPtr.Zero, false, mutexName);
            if (mutexHandle == IntPtr.Zero)
            {
                int error = Marshal.GetLastWin32Error();
                if (error == ERROR_ALREADY_EXISTS)
                {
                    mutexHandle = OpenMutex(wocketPermissions, false, mutexName);
                    if (mutexHandle == IntPtr.Zero)
                    {
                        error = Marshal.GetLastWin32Error();
                        if (error == ERROR_FILE_NOT_FOUND)
                        {
                            //start over: the other process closed between the CreateMutex call
                            //and the OpenMutex call. 

                            return getMutexHandle(mutexName);
                        }
                        else
                            throw new Exception("Couldn't open the wocket Controller mutex: " + error);
                    }
                }
                else
                    throw new Exception("Couldn't get a handle to the controller mutex: " + error);
            }
            return mutexHandle;
            //controllerMutexHandle = mutexHandle;
        }

        internal void WriteFeature(Type sensorType, Feature feature)
        {
            //obtain the IPC mutex
            uint error = WaitForSingleObject(ipcMutexes[sensorType], DEFAULT_WAIT_TIME);
            if (error != 0)
                throw new Exception("Couldn't acquire the IPC mutex for the sensor: " + sensorType.FullName);

            //add to this process's list of features
            Feature match = thisProcessFeatures[sensorType].Find(delegate(Feature feature2) { return feature2.Equals(feature); });
            //if (thisProcessFeatures[sensorType].Contains(feature))
            if (match != null)
            {
                //this only makes sense if the new oldness requirement is higher
                //otherwise, throw an exception
                if (match.RequiredOldness > feature.RequiredOldness) 
                    throw new Exception("Tried to add a feature that already exists");//shouldn't be able to happen
            }
            else
            {
                thisProcessFeatures[sensorType].Add(feature);
            }
            //add to the inter-process list of features
            //first, read all the current features
            openFeatureStreams[sensorType].Seek(0, SeekOrigin.Begin);
            List<Feature> features = new List<Feature>();
            long featurePeriod = openFeatureReaders[sensorType].ReadInt64();
            while (featurePeriod != 0)
            {
                long oldness = openFeatureReaders[sensorType].ReadInt64();
                int versionNumber = openFeatureReaders[sensorType].ReadInt32();
                string featureName = openFeatureReaders[sensorType].ReadString();
                features.Add(new Feature(featureName, TimeSpan.FromTicks(featurePeriod), TimeSpan.FromTicks(oldness), versionNumber));
                featurePeriod = openFeatureReaders[sensorType].ReadInt64();
            }
            match = features.Find(delegate(Feature feature2) { return feature2.Equals(feature); });

            if (match == null)
                features.Add(feature);
            else
            {
                if (match.RequiredOldness < feature.RequiredOldness)
                    match.RequiredOldness = feature.RequiredOldness;
                if (match.VersionNumber < feature.VersionNumber)
                    match.VersionNumber = feature.VersionNumber; 
            }


            //also make sure that all the local process features are in the inter-process list
            foreach (Feature f in thisProcessFeatures[sensorType])
            {
                if (!features.Contains(f))
                    features.Add(f);
            }

            //then write them back
            openFeatureStreams[sensorType].Seek(0, SeekOrigin.Begin);
            foreach (Feature f in features)
            {
                openFeatureWriters[sensorType].Write(f.Period.Ticks);
                openFeatureWriters[sensorType].Write(f.RequiredOldness.Ticks);
                openFeatureWriters[sensorType].Write(f.VersionNumber);
                openFeatureWriters[sensorType].Write(f.Name);
            }

            ReleaseMutex(ipcMutexes[sensorType]);
        }

        internal List<Feature> GetFeatureList(Type sensorType)
        {
            uint error = WaitForSingleObject(ipcMutexes[sensorType], DEFAULT_WAIT_TIME);
            if (error != 0)
                throw new Exception("Couldn't acquire the IPC mutex for the sensor: " + sensorType);
            //read all the inter-process features
            List<Feature> features = new List<Feature>();
            openFeatureStreams[sensorType].Seek(0, SeekOrigin.Begin);
            long featurePeriod = openFeatureReaders[sensorType].ReadInt64();
            while (featurePeriod != 0)
            {
                long oldness = openFeatureReaders[sensorType].ReadInt64();
                int versionNumber = openFeatureReaders[sensorType].ReadInt32();
                string featureName = openFeatureReaders[sensorType].ReadString();
                features.Add(new Feature(featureName, TimeSpan.FromTicks(featurePeriod), TimeSpan.FromTicks(oldness), versionNumber));
                featurePeriod = openFeatureReaders[sensorType].ReadInt64();
            }

            //check whether there are any local features that are not in the
            //inter-process list
            bool localFeatureNotInList = false;
            foreach (Feature f in thisProcessFeatures[sensorType])
            {
                Feature match = features.Find(delegate(Feature feature) { return f.Equals(feature); });
                if (match == null)
                {
                    localFeatureNotInList = true;
                    features.Add(f);   
                } 
                else
                {
                    //if there are two of the same feature, only keep the
                    //longest requiredOldness time.
                    if (f.RequiredOldness > match.RequiredOldness)
                    {
                        localFeatureNotInList = true;
                        match.RequiredOldness = f.RequiredOldness;
                    }
                    if (f.VersionNumber > match.VersionNumber)
                    {
                        localFeatureNotInList = true;
                        match.VersionNumber = f.VersionNumber;
                    }
                }
            }
            //if there are any additional features in the local list, copy them to the global list
            if (localFeatureNotInList)
            {
                openFeatureWriters[sensorType].Seek(0, SeekOrigin.Begin);
                foreach (Feature f in features)
                {
                    openFeatureWriters[sensorType].Write(f.Period.Ticks);
                    openFeatureWriters[sensorType].Write(f.RequiredOldness.Ticks);
                    openFeatureWriters[sensorType].Write(f.VersionNumber);
                    openFeatureWriters[sensorType].Write(f.Name);
                }
            }

            ReleaseMutex(ipcMutexes[sensorType]);
            return features;
        }

        internal void RemoveFeature(Type sensorType, Feature feature)
        {
            //obtain the IPC mutex
            uint error = WaitForSingleObject(ipcMutexes[sensorType], DEFAULT_WAIT_TIME);
            if (error != 0)
                throw new Exception("Couldn't acquire the IPC mutex for the sensor: " + sensorType.FullName);

            //remove from the local features list
            thisProcessFeatures[sensorType].Remove(feature);

            //read all inter-process features
            List<Feature> features = new List<Feature>();
            openFeatureStreams[sensorType].Seek(0, SeekOrigin.Begin);
            long featurePeriod = openFeatureReaders[sensorType].ReadInt64();
            while (featurePeriod != 0)
            {
                long oldness = openFeatureReaders[sensorType].ReadInt64();
                int verionNumber = openFeatureReaders[sensorType].ReadInt32();
                string featureName = openFeatureReaders[sensorType].ReadString();
                features.Add(new Feature(featureName, TimeSpan.FromTicks(featurePeriod), TimeSpan.FromTicks(oldness), verionNumber));
                featurePeriod = openFeatureReaders[sensorType].ReadInt64();
            }
            features.Remove(feature);

            //make sure all the local process features are in the inter-process list
            foreach (Feature f in thisProcessFeatures[sensorType])
            {
                Feature match = features.Find(delegate(Feature feature2) { return f.Equals(feature2); });
                if (match == null)
                {
                    features.Add(f);
                }
                else
                {
                    if (f.RequiredOldness > match.RequiredOldness)
                    {
                        match.RequiredOldness = f.RequiredOldness;
                    }
                    if (f.VersionNumber > match.VersionNumber)
                    {
                        match.VersionNumber = f.VersionNumber;
                    }
                }
            }
            //write back the features
            openFeatureWriters[sensorType].Seek(0, SeekOrigin.Begin);
            foreach (Feature f in features)
            {
                openFeatureWriters[sensorType].Write(f.Period.Ticks);
                openFeatureWriters[sensorType].Write(f.RequiredOldness.Ticks);
                openFeatureWriters[sensorType].Write(f.VersionNumber);
                openFeatureWriters[sensorType].Write(f.Name);
            }
            //fill in the other feature with zeros
            openFeatureWriters[sensorType].Write(0L);//period
            openFeatureWriters[sensorType].Write(0L);//requiredOldness
            openFeatureWriters[sensorType].Write(0);//versionNumber
            openFeatureWriters[sensorType].Write(0);//string length int
            for (int ii = 0; ii < feature.Name.Length; ii++)
            {
                openFeatureWriters[sensorType].Write((byte)0);
            }
            ReleaseMutex(ipcMutexes[sensorType]);
        }

        internal void StopWorking(Type sensorType)
        {
            uint error = WaitForSingleObject(ipcMutexes[sensorType], DEFAULT_WAIT_TIME);
            if (error != 0)
                throw new Exception("couldn't acquire the mutex for sensor type: " + sensorType);
            ipcWriters[sensorType].Seek(0, SeekOrigin.Begin);
            ipcWriters[sensorType].Write(-1);
            ipcWriters[sensorType].Flush();
            ReleaseMutex(ipcMutexes[sensorType]);
        }

        internal void registerSensorType(Type sensorType)
        {
            if (!ipcMutexes.ContainsKey(sensorType))
            {
                ipcMutexes[sensorType] = getMutexHandle(sensorType.FullName + "Mutex");


                //acquire the mutex
                uint errorCode = WaitForSingleObject(ipcMutexes[sensorType], DEFAULT_WAIT_TIME);
                if (errorCode != 0)
                    throw new Exception("Couldn't acquire the ipc mutex for sensor: " + sensorType.FullName);

                //open the mmf, stream, etc.
                try
                {
                    if (ipcMmfs.ContainsKey(sensorType))//this should be impossible
                        throw new Exception("ipcMmfs already has a key for this sensor type: " + sensorType.FullName);

                    ipcMmfs[sensorType] = MemoryMappedFile.Create(null, MapProtection.PageReadWrite, DEFAULT_IPC_MMF_SIZE, sensorType.FullName + "MMF");
                    GC.SuppressFinalize(ipcMmfs[sensorType]);
                    ipcStreams[sensorType] = ipcMmfs[sensorType].MapView(MapAccess.FileMapWrite, 0, DEFAULT_IPC_MMF_SIZE);
                    GC.SuppressFinalize(ipcStreams[sensorType]);
                    ipcReaders[sensorType] = new BinaryReader(ipcStreams[sensorType]);
                    GC.SuppressFinalize(ipcReaders[sensorType]);
                    ipcWriters[sensorType] = new BinaryWriter(ipcStreams[sensorType]);
                    GC.SuppressFinalize(ipcWriters[sensorType]);
                    openFeatureMmfs[sensorType] = MemoryMappedFile.Create(null, MapProtection.PageReadWrite, DEFAULT_IPC_MMF_SIZE, sensorType.FullName + "FeatureList");
                    GC.SuppressFinalize(openFeatureMmfs[sensorType]);
                    openFeatureStreams[sensorType] = openFeatureMmfs[sensorType].MapView(MapAccess.FileMapWrite, 0, DEFAULT_IPC_MMF_SIZE);
                    GC.SuppressFinalize(openFeatureStreams[sensorType]);
                    openFeatureReaders[sensorType] = new BinaryReader(openFeatureStreams[sensorType]);
                    GC.SuppressFinalize(openFeatureReaders[sensorType]);
                    openFeatureWriters[sensorType] = new BinaryWriter(openFeatureStreams[sensorType]);
                    GC.SuppressFinalize(openFeatureWriters[sensorType]);
                    thisProcessFeatures[sensorType] = new List<Feature>();
                    GC.SuppressFinalize(thisProcessFeatures[sensorType]);
                }
                catch (Exception e)
                {
                    throw new Exception("Couldn't open an IPC MMF for sensor " + sensorType.FullName + ". Exception: " + e.ToString());
                }

                //check whether this is the first process to open the IPC MMF for this type
                int ownerProcessID = ipcReaders[sensorType].ReadInt32();
                if (ownerProcessID == 0 || ownerProcessID == -1)
                {
                    ipcWriters[sensorType].Seek(0, SeekOrigin.Begin);
                    ipcWriters[sensorType].Write(processID);
                }

                ReleaseMutex(ipcMutexes[sensorType]);
            }
        }

        //fixed!
        internal bool IsWorkingProcess(Type sensorType)
        {
            bool working = false;
            if (!ipcMutexes.ContainsKey(sensorType))
            {
                //this shouldn't be allowed to happen, since all WocketSensors
                //call registerSensorType first
                throw new Exception("The IPC Mutex for sensor " + sensorType + " doesn't exist!");
            }
            else //it already exists, so just check whether this process owns the MMF
            {
                uint error = WaitForSingleObject(ipcMutexes[sensorType], DEFAULT_WAIT_TIME);
                if (error != 0)
                    throw new Exception("Couldn't acquire the IPC mutex for the sensor type: " + sensorType);

                ipcReaders[sensorType].BaseStream.Seek(0, SeekOrigin.Begin);
                int ownerProcessID = ipcReaders[sensorType].ReadInt32();
                if (ownerProcessID == -1)
                {
                    ipcWriters[sensorType].Seek(0, SeekOrigin.Begin);
                    ipcWriters[sensorType].Write(processID);
                    working = true;
                } 
                else
                    working = ownerProcessID == processID;

                ReleaseMutex(ipcMutexes[sensorType]);
            }

            return working;
        }

        internal Stream ReallocateStream(Type sensorType, Feature f)
        {
            uint error = WaitForSingleObject(ipcMutexes[sensorType], DEFAULT_WAIT_TIME);
            if (error != 0)
                throw new Exception("Timed out waiting for the IPC mutex");

            try
            {
                featureWriterStreams[sensorType][f].Seek(16, SeekOrigin.Begin);
                byte[] intBytes = new byte[4];
                featureWriterStreams[sensorType][f].Read(intBytes, 0, intBytes.Length);
                int previousStreamVersion = BitConverter.ToInt32(intBytes, 0);
                long newSize = featureWriterStreams[sensorType][f].Length * 2;
                MemoryMappedFile newMmf = MemoryMappedFile.Create(null, MapProtection.PageReadWrite, newSize, sensorType + "" + f + "DATA" + previousStreamVersion + 1);
                Stream newWriteStream = newMmf.MapView(MapAccess.FileMapWrite, 0, (int)newSize);
                featureWriterStreams[sensorType][f].Seek(0, SeekOrigin.Begin);
                lock (tempBuffer)
                {
                    long bytesCopied = 0;
                    while (bytesCopied < featureWriterStreams[sensorType][f].Length)
                    {
                        int bytesRead = featureWriterStreams[sensorType][f].Read(tempBuffer, 0, tempBuffer.Length);
                        newWriteStream.Write(tempBuffer, 0, bytesRead);
                        bytesCopied += bytesRead;
                    }
                }
                newWriteStream.Seek(16, SeekOrigin.Begin);
                intBytes = BitConverter.GetBytes(previousStreamVersion + 1);
                newWriteStream.Write(intBytes, 0, intBytes.Length);
                featureWriterStreams[sensorType][f].Seek(16, SeekOrigin.Begin);
                featureWriterStreams[sensorType][f].Write(intBytes, 0, intBytes.Length);
                featureWriterStreams[sensorType][f].Close();
                GC.ReRegisterForFinalize(featureWriterStreams[sensorType][f]);
                featureWriterStreams[sensorType][f] = newWriteStream;
                featureStreamMmfs[sensorType][f].Close();
                GC.ReRegisterForFinalize(featureStreamMmfs[sensorType][f]);
                featureStreamMmfs[sensorType][f] = newMmf;
                GC.SuppressFinalize(newMmf);
                GC.SuppressFinalize(newWriteStream);
                
                return newWriteStream;
            }
            finally
            {
                ReleaseMutex(ipcMutexes[sensorType]);
            }
        }

        internal Stream OpenWriteStream(Type sensorType, Feature f)
        {
            if (!featureStreamMmfs.ContainsKey(sensorType))
            {
                featureStreamMmfs[sensorType] = new Dictionary<Feature, MemoryMappedFile>();
                GC.SuppressFinalize(featureStreamMmfs[sensorType]);
                featureWriterStreams[sensorType] = new Dictionary<Feature, Stream>();
                GC.SuppressFinalize(featureWriterStreams[sensorType]);
            }
            if (!featureStreamMmfs[sensorType].ContainsKey(f))
            {
                //throw new Exception("Can't open a stream for a feature that is already open");

                featureStreamMmfs[sensorType][f] = MemoryMappedFile.Create(null, MapProtection.PageReadWrite, DEFAULT_DATA_MMF_SIZE << f.VersionNumber, sensorType + "" + f + "DATA" + f.VersionNumber);
                GC.SuppressFinalize(featureStreamMmfs[sensorType][f]);
                featureWriterStreams[sensorType][f] = featureStreamMmfs[sensorType][f].MapView(MapAccess.FileMapWrite, 0, DEFAULT_DATA_MMF_SIZE << f.VersionNumber);
                GC.SuppressFinalize(featureWriterStreams[sensorType][f]);
            }
            else
            {
                //check the old versionNumber and update if necessary
                int oldVersionNumber = log2(featureWriterStreams[sensorType][f].Length / DEFAULT_DATA_MMF_SIZE);
                if (oldVersionNumber < f.VersionNumber)
                {
                    MemoryMappedFile newMmf = MemoryMappedFile.Create(null, MapProtection.PageReadWrite, DEFAULT_DATA_MMF_SIZE << f.VersionNumber, sensorType + "" + f + "DATA" + f.VersionNumber);
                    Stream newStream = newMmf.MapView(MapAccess.FileMapWrite, 0, DEFAULT_DATA_MMF_SIZE << f.VersionNumber);
                    GC.ReRegisterForFinalize(featureStreamMmfs[sensorType][f]);
                    GC.ReRegisterForFinalize(featureWriterStreams[sensorType][f]);
                    featureStreamMmfs[sensorType][f] = newMmf;
                    featureWriterStreams[sensorType][f] = newStream;
                    GC.SuppressFinalize(featureStreamMmfs[sensorType][f]);
                    GC.SuppressFinalize(featureWriterStreams[sensorType][f]);
                }
            }

            return featureWriterStreams[sensorType][f];
        }

        private int log2(long x)
        {
            if (x < 0) throw new Exception("can't take the log of a negative number");
            int r = 0;
            while ((x >> r) != 0)
            {
                r++;
            }
            return r - 1; // returns -1 for x==0, floor(log2(x)) otherwise
        }


        
        internal Stream OpenReadStream(Type sensorType, Feature f)
        {
            if (!featureStreamMmfs.ContainsKey(sensorType))
                OpenWriteStream(sensorType, f);
            
            return featureStreamMmfs[sensorType][f].MapView(MapAccess.FileMapRead, 0, (int)featureWriterStreams[sensorType][f].Length);
        }

        //might be useful for closing features...
        internal void CloseStream(Stream stream)
        {
            throw new Exception("The method or operation is not implemented.");

        }
        /*
        [StructLayout(LayoutKind.Sequential)]
        public struct SECURITY_ATTRIBUTES
        {
            public int nLength;
            public IntPtr lpSecurityDescriptor;
            public int bInheritHandle;
        }
        */
        [DllImport("coredll", SetLastError = true, EntryPoint = "CreateMutex", CharSet = CharSet.Auto)]
        private static extern IntPtr CreateMutex(IntPtr attrs, bool initialOwner, string mutexName);

        [DllImport("coredll", SetLastError = true, EntryPoint = "ReleaseMutex", CharSet = CharSet.Auto)]
        private static extern bool ReleaseMutex(IntPtr handle);

        [DllImport("coredll", SetLastError = true, EntryPoint = "OpenMutex", CharSet = CharSet.Auto)]
        private static extern IntPtr OpenMutex(uint desiredAccess, bool inheritAccess, string mutexName);

        [DllImport("coredll", SetLastError = true, EntryPoint = "WaitForSingleObject", CharSet = CharSet.Auto)]
        private static extern uint WaitForSingleObject(IntPtr handle, uint millis);

        [DllImport("coredll", SetLastError = true, EntryPoint = "CloseHandle", CharSet = CharSet.Auto)]
        private static extern bool CloseHandle(IntPtr handle);

    }
}
