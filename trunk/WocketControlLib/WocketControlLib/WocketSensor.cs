using System;
using System.Collections.Generic;
using System.Threading;
using System.IO;
using NLog;
using System.Collections;
namespace WocketControlLib
{
    /*
    public struct WocketCallback
    {
        public TimeSpan callingPeriod;
        public WocketSensor.ReadFeatureDelegate callbackFunction;
        public DateTime lastCall;
        public int lastStreamPos;
        public FeatureStream readStream;
        public WocketCallback(TimeSpan callingPeriodParam, WocketSensor.ReadFeatureDelegate callbackFunctionParam, FeatureStream readStreamParam)
        {
            lastStreamPos = 0;
            callingPeriod = callingPeriodParam;
            callbackFunction = callbackFunctionParam;
            readStream = readStreamParam;
            lastCall = DateTime.Now;
        }
    }
    */
    public abstract class WocketSensor
    {
        
        #region Instance Variables
        /* only one *instance* of each class that implements WocketSensor will
         * be "working" - i.e. have a running thread which communicates with other 
         * processes and calls the sensor's CalculateFeatures() function.
         * 
         * Contrast with the workingProcessDict below, which controls whether
         * or not this *process* is considered "working".
         */
        private bool workingInstance = false;

        //This is very important for keeping track of this sensor's variables
        //in the various static dictionaries below. It is the child type (i.e.
        //the type of the class that inherits from WocketSensor
        private Type sensorType;
        
        //thread-related variables for the working instance
        private Thread workerThread;
        private bool killWorkerThread = false;
        private bool threadRunning = false;

        //this is the last time that the workingThread checked the 
        //inter-process feature list for changes
        private DateTime lastFeatureCheck = DateTime.Now;
        #endregion

        #region Static Variables
        /* similar to the workingInstance variable, except that for each
         * class that implements WocketSensor, there will only one
         * *process* at a time that is "working".
         * 
         * For every sensor type there is one working process on any machine
         * but there is a working instance for every process. The difference
         * between processes is that while the working instance's thread is
         * still active in a non-working process, it doesn't call the sensor's
         * CalculateFeatures() method
         */
        private static Dictionary<Type, bool> workingProcessDict = new Dictionary<Type, bool>();

        //the logger is under-used right now. 
        private static Logger logger = LogManager.GetLogger(typeof(WocketSensor).FullName);

        //holds all the features that are being used in this process
        private static Dictionary<Type, List<Feature>> featureDict = new Dictionary<Type, List<Feature>>();

        //holds the writing streams for each feature
        private static Dictionary<Type, Dictionary<Feature, Stream>> writingStreamDict = new Dictionary<Type, Dictionary<Feature, Stream>>();
        private static Dictionary<Type, Dictionary<Feature, BinaryWriter>> writersDict = new Dictionary<Type, Dictionary<Feature, BinaryWriter>>();
        //This is a monotonically increasing count of the number of bytes that
        //have been written to a given feature
        private static Dictionary<Type, Dictionary<Feature, long>> writeTotals = new Dictionary<Type, Dictionary<Feature, long>>();
        //This keeps track of how many times a writing stream has been
        //re-allocated because it was too small. Every time the stream size
        //is re-allocated it gets doubled from its starting size of 
        //Controller.DEFAULT_DATA_MMF_SIZE
        private static Dictionary<Type, Dictionary<Feature, int>> writerStreamVersionNumbers = new Dictionary<Type, Dictionary<Feature, int>>();
        //holds the reading streams for each feature
        private static Dictionary<Type, Dictionary<Feature, List<FeatureStream>>> readingStreamsDict = new Dictionary<Type, Dictionary<Feature, List<FeatureStream>>>();

        
        /*
        There is one instance for each sensor type
        i.e. there is one static reference to a XSensor
        object, one static reference to a YSensor object, etc.
        each of the instances in this table are the "working"
        instances, which is the only instance of a class that
        actually calls the workFunction().
        */
        private static Dictionary<Type, WocketSensor> instances = new Dictionary<Type, WocketSensor>();
        
        //This must be acquired before operating on the instances hashtable
        private static Mutex instancesMutex = new Mutex(false);
        //protected static WocketSensor instance;
        private static Controller controller = Controller.getInstance();        
        #endregion

        #region constants
        private static TimeSpan MAX_WORK_TIME = TimeSpan.FromMilliseconds(100);
        private static TimeSpan TIME_BETWEEN_FEATURE_LIST_CHECKS = TimeSpan.FromSeconds(4);
        #endregion


        
        
        public WocketSensor() 
        {
            //this type can't be WocketSensor, it will be a child class
            sensorType = this.GetType();
            logger.Debug("Creating a wocket sensor");
            if (!instancesMutex.WaitOne())
                throw new Exception("couldn't acquire the instances mutex");
            if (!instances.ContainsKey(sensorType))
            {
                instances[sensorType] = this;
                workingInstance = true;
                if (!workingProcessDict.ContainsKey(sensorType))
                    workingProcessDict[sensorType] = false;//always set to false until Start() is called

                //this MUST be the sensor's first call to controller
                controller.registerSensorType(sensorType);

                workerThread = new Thread(new ThreadStart(threadFunction));

                featureDict[sensorType] = new List<Feature>();
                writingStreamDict[sensorType] = new Dictionary<Feature, Stream>();
                writersDict[sensorType] = new Dictionary<Feature, BinaryWriter>();
                readingStreamsDict[sensorType] = new Dictionary<Feature, List<FeatureStream>>();
                writeTotals[sensorType] = new Dictionary<Feature, long>();
                writerStreamVersionNumbers[sensorType] = new Dictionary<Feature, int>();
            }
            instancesMutex.ReleaseMutex();
        }
        
        
        //one thread per sensor type runs this function continuously 
        //whenever the sensor is started
        private void threadFunction()
        {
            while (!killWorkerThread)
            {
                Thread.Sleep(getSleepTimeMillis());
                
                //check the inter-process feature list, if necessary
                if (DateTime.Now.Subtract(lastFeatureCheck) > TIME_BETWEEN_FEATURE_LIST_CHECKS)
                {
                    checkFeatureList();
                    //also check whether this has become the working process
                    bool isWorkingNow = controller.IsWorkingProcess(sensorType);

                    //also check whether the underlying stream's version number
                    //has changed (which would necessitate opening a new stream)
                    byte[] tempBuffer = new byte[8];
                    foreach (Feature f in writersDict[sensorType].Keys)
                    {
                        lock (writersDict[sensorType][f])
                        {
                            long originalPosition = writersDict[sensorType][f].BaseStream.Position;
                            writersDict[sensorType][f].BaseStream.Seek(16, SeekOrigin.Begin);
                            writersDict[sensorType][f].BaseStream.Read(tempBuffer, 0, tempBuffer.Length);
                            int versionNumber = BitConverter.ToInt32(tempBuffer, 0);
                            if (versionNumber > writerStreamVersionNumbers[sensorType][f])
                            {
                                f.VersionNumber = versionNumber;
                                writerStreamVersionNumbers[sensorType][f] = versionNumber;
                                writingStreamDict[sensorType][f] = controller.OpenWriteStream(sensorType, f);
                                writersDict[sensorType][f].Close();
                                writersDict[sensorType][f] = new BinaryWriter(writingStreamDict[sensorType][f]);
                                foreach (FeatureStream stream in readingStreamsDict[sensorType][f])
                                {
                                    stream.updateStream(controller.OpenReadStream(sensorType, f));
                                }
                                writersDict[sensorType][f].Seek((int)originalPosition, SeekOrigin.Begin);//probably unneccessary
                            }
                            else
                            {
                                writersDict[sensorType][f].Seek((int)originalPosition, SeekOrigin.Begin);
                            }
                        }
                    }
                    
                    //also check whether this process needs to become the working
                    //process
                    if (isWorkingNow && !workingProcessDict[sensorType])
                    {
                        //this process has become the worker, start the sensor
                        OnStart();
                        //update the write totals, etc
                        foreach (Feature f in writersDict[sensorType].Keys)
                        {
                            writersDict[sensorType][f].BaseStream.Seek(0, SeekOrigin.Begin);
                            writersDict[sensorType][f].BaseStream.Read(tempBuffer, 0, tempBuffer.Length);
                            long newWriteCount = BitConverter.ToInt64(tempBuffer, 0);
                            writeTotals[sensorType][f] = newWriteCount;
                            writersDict[sensorType][f].Seek((int)((newWriteCount % (writersDict[sensorType][f].BaseStream.Length - FeatureStream.RESERVED_BYTES)) + FeatureStream.RESERVED_BYTES), SeekOrigin.Begin);
                        }
                        workingProcessDict[sensorType] = true;
                    }

                    
                }
                
                //update all reading streams
                //specifically, this updates the stream data structure so that it
                //reports the actual number of available values in the underlying
                //stream. 
                foreach (Feature f in readingStreamsDict[sensorType].Keys)
                {
                    foreach (FeatureStream stream in readingStreamsDict[sensorType][f])
                    {
                        stream.updateWriteTotal();
                    }
                }

                if (workingProcessDict[sensorType])
                {
                    //locked to eliminate race conditions with OpenFeature
                    lock (featureDict[sensorType])
                    {
                        //do work
                        DateTime before = DateTime.Now;

                        CalculateFeatures(featureDict[sensorType]);
                        TimeSpan elapsed = DateTime.Now.Subtract(before);
                        if (elapsed > MAX_WORK_TIME)
                            logger.Warn("The sensor " + sensorType + " took longer than the max allowable time to run its work funtion. Elapsed: " + elapsed);
                    }
                }
            }
        }

        /*
         * This is called periodically to check this process's list of features
         * against the global (inter-process) feature list for this sensor
         */
        private void checkFeatureList()
        {
            List<Feature> features = controller.GetFeatureList(sensorType);
            //it's only possible to ADD features by checking the inter-process
            //list. Any features that are to be removed would be removed
            //through controller.RemoveFeature
            lock (featureDict[sensorType])
            {
                featureDict[sensorType] = features;
            }
        }

        /// <summary>
        /// Tell the sensor to start computing features. Any FeatureStreams opened
        /// on this sensor will not produce data until the sensor is started.
        /// </summary>
        public void Start()
        {
            //only start on the real working instance
            if (!workingInstance)
            {
                instances[sensorType].Start();
                return;
            }
            lock (this)
            {
                //only start the thread once
                if (threadRunning)
                    return;
                //check whether we're the working process
                workingProcessDict[sensorType] = controller.IsWorkingProcess(sensorType);

                if (workingProcessDict[sensorType])
                {
                    OnStart();
                    threadRunning = true;
                    workerThread.Start();
                }
            }
        }

        /// <summary>
        /// Tells the sensor to stop producing values. This will affect any
        /// FeatureStream that was opened from the sensor.
        /// </summary>
        public void Stop()
        {
            if (!workingInstance)
            {
                instances[sensorType].Stop();
                return;
            }

            lock (this)
            {
                if (!threadRunning)
                    return;

                
                killWorkerThread = true;
                workerThread.Join();

                if (workingProcessDict[sensorType])
                {
                    controller.StopWorking(sensorType);
                    OnStop();
                }
            }
        }

        /*
         * This is a place where the code could be simplified. I can't think of a way
         * to split these up better, but they are all essentially the same except
         * for the sizeof(type) statements and the types of the buffers.
         * Is it possible to to take an object and a type and cast the
         * object as an array of the type?
         */
        #region writeFeautureValues Overrides
        protected void writeFeatureValues(byte[] buffer, int offset, int length, Feature f) 
        {
            if (length * sizeof(byte) > writingStreamDict[sensorType][f].Length)
            {
                //throw new Exception("Can't write this many feature values at once. I should fix this!");
                long lastPosition = writingStreamDict[sensorType][f].Position;
                writingStreamDict[sensorType][f] = controller.ReallocateStream(sensorType, f);
                writingStreamDict[sensorType][f].Seek(lastPosition, SeekOrigin.Begin);
                writersDict[sensorType][f] = new BinaryWriter(writingStreamDict[sensorType][f]);
                writerStreamVersionNumbers[sensorType][f]++;
                foreach (FeatureStream stream in readingStreamsDict[sensorType][f])
                {
                    stream.updateStream(controller.OpenReadStream(sensorType, f));
                }
            }

            int bufferLeft = (int)(writingStreamDict[sensorType][f].Length - writingStreamDict[sensorType][f].Position);
            bufferLeft /= sizeof(byte);
            int ii;
            for (ii = 0; ii < length && ii < bufferLeft; ii++)
            {
                writersDict[sensorType][f].Write(buffer[offset + ii]);
            }
            if (ii != length)
            {
                //now we've written right up to the end of the stream. We need
                //to wrap around and continue writing. However, when we wrap
                //we first need to check that the data we're about to overwrite
                //isn't necessary for some feature. Features indicate how long
                //they need data to be valid by their requiredOldness parameter,
                //which goes in the second 8-byte long in the stream.

                bool wrap = true;
                long writePosition = writingStreamDict[sensorType][f].Position;
                //check the timestamp, and re-allocate if this is too late
                writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                byte[] longBytes = new byte[8];
                writingStreamDict[sensorType][f].Read(longBytes, 0, longBytes.Length);
                long lastWraparoundTicks = BitConverter.ToInt64(longBytes, 0);
                if (lastWraparoundTicks != 0)
                {
                    DateTime lastWraparound = DateTime.FromFileTime(lastWraparoundTicks);
                    TimeSpan sinceLastWraparound = DateTime.Now.Subtract(lastWraparound);
                    if (sinceLastWraparound < f.RequiredOldness)
                    {
                        //re-allocate
                        
                        writingStreamDict[sensorType][f] = controller.ReallocateStream(sensorType, f);
                        
                        writersDict[sensorType][f] = new BinaryWriter(writingStreamDict[sensorType][f]);
                        writerStreamVersionNumbers[sensorType][f]++;
                        foreach (FeatureStream featureStream in readingStreamsDict[sensorType][f])
                        {
                            featureStream.updateStream(controller.OpenReadStream(sensorType, f));
                        }
                        //don't wrap because we just re-allocated
                        wrap = false;
                    }
                    longBytes = BitConverter.GetBytes(DateTime.Now.ToFileTime());
                    writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                    writingStreamDict[sensorType][f].Write(longBytes, 0, longBytes.Length);
                    writingStreamDict[sensorType][f].Seek(writePosition, SeekOrigin.Begin);
                }
                else
                {
                    //lastwraparound time was zero, this is the first time through
                    writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                    longBytes = BitConverter.GetBytes(DateTime.Now.ToFileTime());
                    writingStreamDict[sensorType][f].Write(longBytes, 0, longBytes.Length);
                    writingStreamDict[sensorType][f].Seek(writePosition, SeekOrigin.Begin);
                }


                if (wrap)
                    writingStreamDict[sensorType][f].Seek(FeatureStream.RESERVED_BYTES, SeekOrigin.Begin);  
                
                
                for (; ii < length; ii++)
                {
                    writersDict[sensorType][f].Write(buffer[offset + ii]);
                }
            }
            writersDict[sensorType][f].Flush();
            long position = writingStreamDict[sensorType][f].Position;
            writersDict[sensorType][f].Seek(0, SeekOrigin.Begin);
            long newWriteTotal = writeTotals[sensorType][f] + ii * sizeof(byte);
            writersDict[sensorType][f].Write(newWriteTotal);
            writersDict[sensorType][f].Flush();
            writersDict[sensorType][f].BaseStream.Seek(position, SeekOrigin.Begin);
            writeTotals[sensorType][f] = newWriteTotal;
        }
        protected void writeFeatureValues(int[] buffer, int offset, int length, Feature f)
        {
            if (length * sizeof(int) > writingStreamDict[sensorType][f].Length)
            {
                //throw new Exception("Can't write this many feature values at once. I should fix this!");
                long lastPosition = writingStreamDict[sensorType][f].Position;
                writingStreamDict[sensorType][f] = controller.ReallocateStream(sensorType, f);
                writingStreamDict[sensorType][f].Seek(lastPosition, SeekOrigin.Begin);
                writersDict[sensorType][f] = new BinaryWriter(writingStreamDict[sensorType][f]);
                writerStreamVersionNumbers[sensorType][f]++;
                foreach (FeatureStream stream in readingStreamsDict[sensorType][f])
                {
                    stream.updateStream(controller.OpenReadStream(sensorType, f));
                }
            }

            int bufferLeft = (int)(writingStreamDict[sensorType][f].Length - writingStreamDict[sensorType][f].Position);
            bufferLeft /= sizeof(int);
            int ii;
            for (ii = 0; ii < length && ii < bufferLeft; ii++)
            {
                writersDict[sensorType][f].Write(buffer[offset + ii]);
            }
            if (ii != length)
            {
                //now we've written right up to the end of the stream. We need
                //to wrap around and continue writing. However, when we wrap
                //we first need to check that the data we're about to overwrite
                //isn't necessary for some feature. Features indicate how long
                //they need data to be valid by their requiredOldness parameter,
                //which goes in the second 8-byte long in the stream.

                bool wrap = true;
                long writePosition = writingStreamDict[sensorType][f].Position;
                //check the timestamp, and re-allocate if this is too late
                writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                byte[] longBytes = new byte[8];
                writingStreamDict[sensorType][f].Read(longBytes, 0, longBytes.Length);
                long lastWraparoundTicks = BitConverter.ToInt64(longBytes, 0);
                if (lastWraparoundTicks != 0)
                {
                    DateTime lastWraparound = DateTime.FromFileTime(lastWraparoundTicks);
                    TimeSpan sinceLastWraparound = DateTime.Now.Subtract(lastWraparound);
                    if (sinceLastWraparound < f.RequiredOldness)
                    {
                        //re-allocate
                        writingStreamDict[sensorType][f] = controller.ReallocateStream(sensorType, f);
                        
                        writersDict[sensorType][f] = new BinaryWriter(writingStreamDict[sensorType][f]);
                        writerStreamVersionNumbers[sensorType][f]++;
                        foreach (FeatureStream featureStream in readingStreamsDict[sensorType][f])
                        {
                            featureStream.updateStream(controller.OpenReadStream(sensorType, f));
                        }
                        //don't wrap because we just re-allocated
                        wrap = false;
                    }
                    longBytes = BitConverter.GetBytes(DateTime.Now.ToFileTime());
                    writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                    writingStreamDict[sensorType][f].Write(longBytes, 0, longBytes.Length);
                    writingStreamDict[sensorType][f].Seek(writePosition, SeekOrigin.Begin);
                }
                else
                {
                    //lastwraparound time was zero, this is the first time through
                    writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                    longBytes = BitConverter.GetBytes(DateTime.Now.ToFileTime());
                    writingStreamDict[sensorType][f].Write(longBytes, 0, longBytes.Length);
                    writingStreamDict[sensorType][f].Seek(writePosition, SeekOrigin.Begin);
                }
                
                
                if (wrap)
                    writingStreamDict[sensorType][f].Seek(FeatureStream.RESERVED_BYTES, SeekOrigin.Begin);  
                
                for (; ii < length; ii++)
                {
                    writersDict[sensorType][f].Write(buffer[offset + ii]);
                }
            }
            writersDict[sensorType][f].Flush();
            long position = writingStreamDict[sensorType][f].Position;
            writersDict[sensorType][f].Seek(0, SeekOrigin.Begin);
            long newWriteTotal = writeTotals[sensorType][f] + ii * sizeof(int);
            writersDict[sensorType][f].Write(newWriteTotal);
            writersDict[sensorType][f].Flush();
            writersDict[sensorType][f].BaseStream.Seek(position, SeekOrigin.Begin);
            writeTotals[sensorType][f] = newWriteTotal;
        }
        protected void writeFeatureValues(uint[] buffer, int offset, int length, Feature f)
        {
            if (length * sizeof(uint) > writingStreamDict[sensorType][f].Length)
            {
                //throw new Exception("Can't write this many feature values at once. I should fix this!");
                long lastPosition = writingStreamDict[sensorType][f].Position;
                writingStreamDict[sensorType][f] = controller.ReallocateStream(sensorType, f);
                writingStreamDict[sensorType][f].Seek(lastPosition, SeekOrigin.Begin);
                writersDict[sensorType][f] = new BinaryWriter(writingStreamDict[sensorType][f]);
                writerStreamVersionNumbers[sensorType][f]++;
                foreach (FeatureStream stream in readingStreamsDict[sensorType][f])
                {
                    stream.updateStream(controller.OpenReadStream(sensorType, f));
                }
            }

            int bufferLeft = (int)(writingStreamDict[sensorType][f].Length - writingStreamDict[sensorType][f].Position);
            bufferLeft /= sizeof(uint);
            int ii;
            for (ii = 0; ii < length && ii < bufferLeft; ii++)
            {
                writersDict[sensorType][f].Write(buffer[offset + ii]);
            }
            if (ii != length)
            {
                //now we've written right up to the end of the stream. We need
                //to wrap around and continue writing. However, when we wrap
                //we first need to check that the data we're about to overwrite
                //isn't necessary for some feature. Features indicate how long
                //they need data to be valid by their requiredOldness parameter,
                //which goes in the second 8-byte long in the stream.

                bool wrap = true;
                long writePosition = writingStreamDict[sensorType][f].Position;
                //check the timestamp, and re-allocate if this is too late
                writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                byte[] longBytes = new byte[8];
                writingStreamDict[sensorType][f].Read(longBytes, 0, longBytes.Length);
                long lastWraparoundTicks = BitConverter.ToInt64(longBytes, 0);
                if (lastWraparoundTicks != 0)
                {
                    DateTime lastWraparound = DateTime.FromFileTime(lastWraparoundTicks);
                    TimeSpan sinceLastWraparound = DateTime.Now.Subtract(lastWraparound);
                    if (sinceLastWraparound < f.RequiredOldness)
                    {
                        //re-allocate
                        
                        writingStreamDict[sensorType][f] = controller.ReallocateStream(sensorType, f);
                        
                        writersDict[sensorType][f] = new BinaryWriter(writingStreamDict[sensorType][f]);
                        writerStreamVersionNumbers[sensorType][f]++;
                        foreach (FeatureStream featureStream in readingStreamsDict[sensorType][f])
                        {
                            featureStream.updateStream(controller.OpenReadStream(sensorType, f));
                        }
                        //don't wrap because we just re-allocated
                        wrap = false;
                    }
                    longBytes = BitConverter.GetBytes(DateTime.Now.ToFileTime());
                    writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                    writingStreamDict[sensorType][f].Write(longBytes, 0, longBytes.Length);
                    writingStreamDict[sensorType][f].Seek(writePosition, SeekOrigin.Begin);
                }
                else
                {
                    //lastwraparound time was zero, this is the first time through
                    writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                    longBytes = BitConverter.GetBytes(DateTime.Now.ToFileTime());
                    writingStreamDict[sensorType][f].Write(longBytes, 0, longBytes.Length);
                    writingStreamDict[sensorType][f].Seek(writePosition, SeekOrigin.Begin);
                }


                if (wrap)
                    writingStreamDict[sensorType][f].Seek(FeatureStream.RESERVED_BYTES, SeekOrigin.Begin);  
                
                
                for (; ii < length; ii++)
                {
                    writersDict[sensorType][f].Write(buffer[offset + ii]);
                }
            }
            writersDict[sensorType][f].Flush();
            long position = writingStreamDict[sensorType][f].Position;
            writersDict[sensorType][f].Seek(0, SeekOrigin.Begin);
            long newWriteTotal = writeTotals[sensorType][f] + ii * sizeof(uint);
            writersDict[sensorType][f].Write(newWriteTotal);
            writersDict[sensorType][f].Flush();
            writersDict[sensorType][f].BaseStream.Seek(position, SeekOrigin.Begin);
            writeTotals[sensorType][f] = newWriteTotal;
        }
        protected void writeFeatureValues(short[] buffer, int offset, int length, Feature f)
        {

            if (length * sizeof(short) > writingStreamDict[sensorType][f].Length)
            {
                //throw new Exception("Can't write this many feature values at once. I should fix this!");
                long lastPosition = writingStreamDict[sensorType][f].Position;
                writingStreamDict[sensorType][f] = controller.ReallocateStream(sensorType, f);
                writingStreamDict[sensorType][f].Seek(lastPosition, SeekOrigin.Begin);
                writersDict[sensorType][f] = new BinaryWriter(writingStreamDict[sensorType][f]);
                writerStreamVersionNumbers[sensorType][f]++;
                foreach (FeatureStream stream in readingStreamsDict[sensorType][f])
                {
                    stream.updateStream(controller.OpenReadStream(sensorType, f));
                }
            }

            int bufferLeft = (int)(writingStreamDict[sensorType][f].Length - writingStreamDict[sensorType][f].Position);
            bufferLeft /= sizeof(short);
            int ii;
            for (ii = 0; ii < length && ii < bufferLeft; ii++)
            {
                writersDict[sensorType][f].Write(buffer[offset + ii]);
            }
            if (ii != length)
            {
                //now we've written right up to the end of the stream. We need
                //to wrap around and continue writing. However, when we wrap
                //we first need to check that the data we're about to overwrite
                //isn't necessary for some feature. Features indicate how long
                //they need data to be valid by their requiredOldness parameter,
                //which goes in the second 8-byte long in the stream.

                bool wrap = true;
                long writePosition = writingStreamDict[sensorType][f].Position;
                //check the timestamp, and re-allocate if this is too late
                writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                byte[] longBytes = new byte[8];
                writingStreamDict[sensorType][f].Read(longBytes, 0, longBytes.Length);
                long lastWraparoundTicks = BitConverter.ToInt64(longBytes, 0);
                if (lastWraparoundTicks != 0)
                {
                    DateTime lastWraparound = DateTime.FromFileTime(lastWraparoundTicks);
                    TimeSpan sinceLastWraparound = DateTime.Now.Subtract(lastWraparound);
                    if (sinceLastWraparound < f.RequiredOldness)
                    {
                        //re-allocate
                        
                        writingStreamDict[sensorType][f] = controller.ReallocateStream(sensorType, f);
                        
                        writersDict[sensorType][f] = new BinaryWriter(writingStreamDict[sensorType][f]);
                        writerStreamVersionNumbers[sensorType][f]++;
                        foreach (FeatureStream featureStream in readingStreamsDict[sensorType][f])
                        {
                            featureStream.updateStream(controller.OpenReadStream(sensorType, f));
                        }
                        //don't wrap because we just re-allocated
                        wrap = false;
                    }
                    longBytes = BitConverter.GetBytes(DateTime.Now.ToFileTime());
                    writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                    writingStreamDict[sensorType][f].Write(longBytes, 0, longBytes.Length);
                    writingStreamDict[sensorType][f].Seek(writePosition, SeekOrigin.Begin);
                }
                else
                {
                    //lastwraparound time was zero, this is the first time through
                    writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                    longBytes = BitConverter.GetBytes(DateTime.Now.ToFileTime());
                    writingStreamDict[sensorType][f].Write(longBytes, 0, longBytes.Length);
                    writingStreamDict[sensorType][f].Seek(writePosition, SeekOrigin.Begin);
                }


                if (wrap)
                    writingStreamDict[sensorType][f].Seek(FeatureStream.RESERVED_BYTES, SeekOrigin.Begin);  
                
                
                for (; ii < length; ii++)
                {
                    writersDict[sensorType][f].Write(buffer[offset + ii]);
                }
            }
            writersDict[sensorType][f].Flush();
            long position = writingStreamDict[sensorType][f].Position;
            writersDict[sensorType][f].Seek(0, SeekOrigin.Begin);
            long newWriteTotal = writeTotals[sensorType][f] + ii * sizeof(short);
            writersDict[sensorType][f].Write(newWriteTotal);
            writersDict[sensorType][f].Flush();
            writersDict[sensorType][f].BaseStream.Seek(position, SeekOrigin.Begin);
            writeTotals[sensorType][f] = newWriteTotal;
            
        }
        protected void writeFeatureValues(ushort[] buffer, int offset, int length, Feature f)
        {
            if (length * sizeof(ushort) > writingStreamDict[sensorType][f].Length)
            {
                //throw new Exception("Can't write this many feature values at once. I should fix this!");
                long lastPosition = writingStreamDict[sensorType][f].Position;
                writingStreamDict[sensorType][f] = controller.ReallocateStream(sensorType, f);
                writingStreamDict[sensorType][f].Seek(lastPosition, SeekOrigin.Begin);
                writersDict[sensorType][f] = new BinaryWriter(writingStreamDict[sensorType][f]);
                writerStreamVersionNumbers[sensorType][f]++;
                foreach (FeatureStream stream in readingStreamsDict[sensorType][f])
                {
                    stream.updateStream(controller.OpenReadStream(sensorType, f));
                }
            }

            int bufferLeft = (int)(writingStreamDict[sensorType][f].Length - writingStreamDict[sensorType][f].Position);
            bufferLeft /= sizeof(ushort);
            int ii;
            for (ii = 0; ii < length && ii < bufferLeft; ii++)
            {
                writersDict[sensorType][f].Write(buffer[offset + ii]);
            }
            if (ii != length)
            {
                //now we've written right up to the end of the stream. We need
                //to wrap around and continue writing. However, when we wrap
                //we first need to check that the data we're about to overwrite
                //isn't necessary for some feature. Features indicate how long
                //they need data to be valid by their requiredOldness parameter,
                //which goes in the second 8-byte long in the stream.

                bool wrap = true;
                long writePosition = writingStreamDict[sensorType][f].Position;
                //check the timestamp, and re-allocate if this is too late
                writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                byte[] longBytes = new byte[8];
                writingStreamDict[sensorType][f].Read(longBytes, 0, longBytes.Length);
                long lastWraparoundTicks = BitConverter.ToInt64(longBytes, 0);
                if (lastWraparoundTicks != 0)
                {
                    DateTime lastWraparound = DateTime.FromFileTime(lastWraparoundTicks);
                    TimeSpan sinceLastWraparound = DateTime.Now.Subtract(lastWraparound);
                    if (sinceLastWraparound < f.RequiredOldness)
                    {
                        //re-allocate
                        
                        writingStreamDict[sensorType][f] = controller.ReallocateStream(sensorType, f);
                        
                        writersDict[sensorType][f] = new BinaryWriter(writingStreamDict[sensorType][f]);
                        writerStreamVersionNumbers[sensorType][f]++;
                        foreach (FeatureStream featureStream in readingStreamsDict[sensorType][f])
                        {
                            featureStream.updateStream(controller.OpenReadStream(sensorType, f));
                        }
                        //don't wrap because we just re-allocated
                        wrap = false;
                    }
                    longBytes = BitConverter.GetBytes(DateTime.Now.ToFileTime());
                    writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                    writingStreamDict[sensorType][f].Write(longBytes, 0, longBytes.Length);
                    writingStreamDict[sensorType][f].Seek(writePosition, SeekOrigin.Begin);
                }
                else
                {
                    //lastwraparound time was zero, this is the first time through
                    writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                    longBytes = BitConverter.GetBytes(DateTime.Now.ToFileTime());
                    writingStreamDict[sensorType][f].Write(longBytes, 0, longBytes.Length);
                    writingStreamDict[sensorType][f].Seek(writePosition, SeekOrigin.Begin);
                }


                if (wrap)
                    writingStreamDict[sensorType][f].Seek(FeatureStream.RESERVED_BYTES, SeekOrigin.Begin);  
                
                
                for (; ii < length; ii++)
                {
                    writersDict[sensorType][f].Write(buffer[offset + ii]);
                }
            }
            writersDict[sensorType][f].Flush();
            long position = writingStreamDict[sensorType][f].Position;
            writersDict[sensorType][f].Seek(0, SeekOrigin.Begin);
            long newWriteTotal = writeTotals[sensorType][f] + ii * sizeof(ushort);
            writersDict[sensorType][f].Write(newWriteTotal);
            writersDict[sensorType][f].Flush();
            writersDict[sensorType][f].BaseStream.Seek(position, SeekOrigin.Begin);
            writeTotals[sensorType][f] = newWriteTotal;
        }
        protected void writeFeatureValues(long[] buffer, int offset, int length, Feature f)
        {
            if (length * sizeof(long) > writingStreamDict[sensorType][f].Length)
            {
                //throw new Exception("Can't write this many feature values at once. I should fix this!");
                long lastPosition = writingStreamDict[sensorType][f].Position;
                writingStreamDict[sensorType][f] = controller.ReallocateStream(sensorType, f);
                writingStreamDict[sensorType][f].Seek(lastPosition, SeekOrigin.Begin);
                writersDict[sensorType][f] = new BinaryWriter(writingStreamDict[sensorType][f]);
                writerStreamVersionNumbers[sensorType][f]++;
                foreach (FeatureStream stream in readingStreamsDict[sensorType][f])
                {
                    stream.updateStream(controller.OpenReadStream(sensorType, f));
                }
            }

            int bufferLeft = (int)(writingStreamDict[sensorType][f].Length - writingStreamDict[sensorType][f].Position);
            bufferLeft /= sizeof(long);
            int ii;
            for (ii = 0; ii < length && ii < bufferLeft; ii++)
            {
                writersDict[sensorType][f].Write(buffer[offset + ii]);
            }
            if (ii != length)
            {
                //now we've written right up to the end of the stream. We need
                //to wrap around and continue writing. However, when we wrap
                //we first need to check that the data we're about to overwrite
                //isn't necessary for some feature. Features indicate how long
                //they need data to be valid by their requiredOldness parameter,
                //which goes in the second 8-byte long in the stream.

                bool wrap = true;
                long writePosition = writingStreamDict[sensorType][f].Position;
                //check the timestamp, and re-allocate if this is too late
                writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                byte[] longBytes = new byte[8];
                writingStreamDict[sensorType][f].Read(longBytes, 0, longBytes.Length);
                long lastWraparoundTicks = BitConverter.ToInt64(longBytes, 0);
                if (lastWraparoundTicks != 0)
                {
                    DateTime lastWraparound = DateTime.FromFileTime(lastWraparoundTicks);
                    TimeSpan sinceLastWraparound = DateTime.Now.Subtract(lastWraparound);
                    if (sinceLastWraparound < f.RequiredOldness)
                    {
                        //re-allocate
                        
                        writingStreamDict[sensorType][f] = controller.ReallocateStream(sensorType, f);
                        
                        writersDict[sensorType][f] = new BinaryWriter(writingStreamDict[sensorType][f]);
                        writerStreamVersionNumbers[sensorType][f]++;
                        foreach (FeatureStream featureStream in readingStreamsDict[sensorType][f])
                        {
                            featureStream.updateStream(controller.OpenReadStream(sensorType, f));
                        }
                        //don't wrap because we just re-allocated
                        wrap = false;
                    }
                    longBytes = BitConverter.GetBytes(DateTime.Now.ToFileTime());
                    writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                    writingStreamDict[sensorType][f].Write(longBytes, 0, longBytes.Length);
                    writingStreamDict[sensorType][f].Seek(writePosition, SeekOrigin.Begin);
                }
                else
                {
                    //lastwraparound time was zero, this is the first time through
                    writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                    longBytes = BitConverter.GetBytes(DateTime.Now.ToFileTime());
                    writingStreamDict[sensorType][f].Write(longBytes, 0, longBytes.Length);
                    writingStreamDict[sensorType][f].Seek(writePosition, SeekOrigin.Begin);
                }


                if (wrap)
                    writingStreamDict[sensorType][f].Seek(FeatureStream.RESERVED_BYTES, SeekOrigin.Begin);  
                
                
                for (; ii < length; ii++)
                {
                    writersDict[sensorType][f].Write(buffer[offset + ii]);
                }
            }
            writersDict[sensorType][f].Flush();
            long position = writingStreamDict[sensorType][f].Position;
            writersDict[sensorType][f].Seek(0, SeekOrigin.Begin);
            long newWriteTotal = writeTotals[sensorType][f] + ii * sizeof(long);
            writersDict[sensorType][f].Write(newWriteTotal);
            writersDict[sensorType][f].Flush();
            writersDict[sensorType][f].BaseStream.Seek(position, SeekOrigin.Begin);
            writeTotals[sensorType][f] = newWriteTotal;
        }
        protected void writeFeatureValues(ulong[] buffer, int offset, int length, Feature f)
        {
            if (length * sizeof(ulong) > writingStreamDict[sensorType][f].Length)
            {
                //throw new Exception("Can't write this many feature values at once. I should fix this!");
                long lastPosition = writingStreamDict[sensorType][f].Position;
                writingStreamDict[sensorType][f] = controller.ReallocateStream(sensorType, f);
                writingStreamDict[sensorType][f].Seek(lastPosition, SeekOrigin.Begin);
                writersDict[sensorType][f] = new BinaryWriter(writingStreamDict[sensorType][f]);
                writerStreamVersionNumbers[sensorType][f]++;
                foreach (FeatureStream stream in readingStreamsDict[sensorType][f])
                {
                    stream.updateStream(controller.OpenReadStream(sensorType, f));
                }
            }

            int bufferLeft = (int)(writingStreamDict[sensorType][f].Length - writingStreamDict[sensorType][f].Position);
            bufferLeft /= sizeof(ulong);
            int ii;
            for (ii = 0; ii < length && ii < bufferLeft; ii++)
            {
                writersDict[sensorType][f].Write(buffer[offset + ii]);
            }
            if (ii != length)
            {
                //now we've written right up to the end of the stream. We need
                //to wrap around and continue writing. However, when we wrap
                //we first need to check that the data we're about to overwrite
                //isn't necessary for some feature. Features indicate how long
                //they need data to be valid by their requiredOldness parameter,
                //which goes in the second 8-byte long in the stream.

                bool wrap = true;
                long writePosition = writingStreamDict[sensorType][f].Position;
                //check the timestamp, and re-allocate if this is too late
                writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                byte[] longBytes = new byte[8];
                writingStreamDict[sensorType][f].Read(longBytes, 0, longBytes.Length);
                long lastWraparoundTicks = BitConverter.ToInt64(longBytes, 0);
                if (lastWraparoundTicks != 0)
                {
                    DateTime lastWraparound = DateTime.FromFileTime(lastWraparoundTicks);
                    TimeSpan sinceLastWraparound = DateTime.Now.Subtract(lastWraparound);
                    if (sinceLastWraparound < f.RequiredOldness)
                    {
                        //re-allocate
                        
                        writingStreamDict[sensorType][f] = controller.ReallocateStream(sensorType, f);
                        
                        writersDict[sensorType][f] = new BinaryWriter(writingStreamDict[sensorType][f]);
                        writerStreamVersionNumbers[sensorType][f]++;
                        foreach (FeatureStream featureStream in readingStreamsDict[sensorType][f])
                        {
                            featureStream.updateStream(controller.OpenReadStream(sensorType, f));
                        }
                        //don't wrap because we just re-allocated
                        wrap = false;
                    }
                    longBytes = BitConverter.GetBytes(DateTime.Now.ToFileTime());
                    writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                    writingStreamDict[sensorType][f].Write(longBytes, 0, longBytes.Length);
                    writingStreamDict[sensorType][f].Seek(writePosition, SeekOrigin.Begin);
                }
                else
                {
                    //lastwraparound time was zero, this is the first time through
                    writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                    longBytes = BitConverter.GetBytes(DateTime.Now.ToFileTime());
                    writingStreamDict[sensorType][f].Write(longBytes, 0, longBytes.Length);
                    writingStreamDict[sensorType][f].Seek(writePosition, SeekOrigin.Begin);
                }


                if (wrap)
                    writingStreamDict[sensorType][f].Seek(FeatureStream.RESERVED_BYTES, SeekOrigin.Begin);  
                
                
                for (; ii < length; ii++)
                {
                    writersDict[sensorType][f].Write(buffer[offset + ii]);
                }
            }
            writersDict[sensorType][f].Flush();
            long position = writingStreamDict[sensorType][f].Position;
            writersDict[sensorType][f].Seek(0, SeekOrigin.Begin);
            long newWriteTotal = writeTotals[sensorType][f] + ii * sizeof(ulong);
            writersDict[sensorType][f].Write(newWriteTotal);
            writersDict[sensorType][f].Flush();
            writersDict[sensorType][f].BaseStream.Seek(position, SeekOrigin.Begin);
            writeTotals[sensorType][f] = newWriteTotal;
        }
        protected void writeFeatureValues(float[] buffer, int offset, int length, Feature f)
        {
            if (length * sizeof(float) > writingStreamDict[sensorType][f].Length)
            {
                //throw new Exception("Can't write this many feature values at once. I should fix this!");
                long lastPosition = writingStreamDict[sensorType][f].Position;
                writingStreamDict[sensorType][f] = controller.ReallocateStream(sensorType, f);
                writingStreamDict[sensorType][f].Seek(lastPosition, SeekOrigin.Begin);
                writersDict[sensorType][f] = new BinaryWriter(writingStreamDict[sensorType][f]);
                writerStreamVersionNumbers[sensorType][f]++;
                foreach (FeatureStream stream in readingStreamsDict[sensorType][f])
                {
                    stream.updateStream(controller.OpenReadStream(sensorType, f));
                }
            }

            int bufferLeft = (int)(writingStreamDict[sensorType][f].Length - writingStreamDict[sensorType][f].Position);
            bufferLeft /= sizeof(float);
            int ii;
            for (ii = 0; ii < length && ii < bufferLeft; ii++)
            {
                writersDict[sensorType][f].Write(buffer[offset + ii]);
            }
            if (ii != length)
            {
                //now we've written right up to the end of the stream. We need
                //to wrap around and continue writing. However, when we wrap
                //we first need to check that the data we're about to overwrite
                //isn't necessary for some feature. Features indicate how long
                //they need data to be valid by their requiredOldness parameter,
                //which goes in the second 8-byte long in the stream.

                bool wrap = true;
                long writePosition = writingStreamDict[sensorType][f].Position;
                //check the timestamp, and re-allocate if this is too late
                writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                byte[] longBytes = new byte[8];
                writingStreamDict[sensorType][f].Read(longBytes, 0, longBytes.Length);
                long lastWraparoundTicks = BitConverter.ToInt64(longBytes, 0);
                if (lastWraparoundTicks != 0)
                {
                    DateTime lastWraparound = DateTime.FromFileTime(lastWraparoundTicks);
                    TimeSpan sinceLastWraparound = DateTime.Now.Subtract(lastWraparound);
                    if (sinceLastWraparound < f.RequiredOldness)
                    {
                        //re-allocate
                        
                        writingStreamDict[sensorType][f] = controller.ReallocateStream(sensorType, f);
                        
                        writersDict[sensorType][f] = new BinaryWriter(writingStreamDict[sensorType][f]);
                        writerStreamVersionNumbers[sensorType][f]++;
                        foreach (FeatureStream featureStream in readingStreamsDict[sensorType][f])
                        {
                            featureStream.updateStream(controller.OpenReadStream(sensorType, f));
                        }
                        //don't wrap because we just re-allocated
                        wrap = false;
                    }
                    longBytes = BitConverter.GetBytes(DateTime.Now.ToFileTime());
                    writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                    writingStreamDict[sensorType][f].Write(longBytes, 0, longBytes.Length);
                    writingStreamDict[sensorType][f].Seek(writePosition, SeekOrigin.Begin);
                }
                else
                {
                    //lastwraparound time was zero, this is the first time through
                    writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                    longBytes = BitConverter.GetBytes(DateTime.Now.ToFileTime());
                    writingStreamDict[sensorType][f].Write(longBytes, 0, longBytes.Length);
                    writingStreamDict[sensorType][f].Seek(writePosition, SeekOrigin.Begin);
                }


                if (wrap)
                    writingStreamDict[sensorType][f].Seek(FeatureStream.RESERVED_BYTES, SeekOrigin.Begin);  
                
                
                for (; ii < length; ii++)
                {
                    writersDict[sensorType][f].Write(buffer[offset + ii]);
                }
            }
            writersDict[sensorType][f].Flush();
            long position = writingStreamDict[sensorType][f].Position;
            writersDict[sensorType][f].Seek(0, SeekOrigin.Begin);
            long newWriteTotal = writeTotals[sensorType][f] + ii * sizeof(float);
            writersDict[sensorType][f].Write(newWriteTotal);
            writersDict[sensorType][f].Flush();
            writersDict[sensorType][f].BaseStream.Seek(position, SeekOrigin.Begin);
            writeTotals[sensorType][f] = newWriteTotal;
        }
        protected void writeFeatureValues(double[] buffer, int offset, int length, Feature f)
        {
            if (length * sizeof(double) > writingStreamDict[sensorType][f].Length)
            {
                //throw new Exception("Can't write this many feature values at once. I should fix this!");
                long lastPosition = writingStreamDict[sensorType][f].Position;
                writingStreamDict[sensorType][f] = controller.ReallocateStream(sensorType, f);
                writingStreamDict[sensorType][f].Seek(lastPosition, SeekOrigin.Begin);
                writersDict[sensorType][f] = new BinaryWriter(writingStreamDict[sensorType][f]);
                writerStreamVersionNumbers[sensorType][f]++;
                foreach (FeatureStream stream in readingStreamsDict[sensorType][f])
                {
                    stream.updateStream(controller.OpenReadStream(sensorType, f));
                }
            }

            int bufferLeft = (int)(writingStreamDict[sensorType][f].Length - writingStreamDict[sensorType][f].Position);
            bufferLeft /= sizeof(double);
            int ii;
            for (ii = 0; ii < length && ii < bufferLeft; ii++)
            {
                writersDict[sensorType][f].Write(buffer[offset + ii]);
            }
            if (ii != length)
            {
                //now we've written right up to the end of the stream. We need
                //to wrap around and continue writing. However, when we wrap
                //we first need to check that the data we're about to overwrite
                //isn't necessary for some feature. Features indicate how long
                //they need data to be valid by their requiredOldness parameter,
                //which goes in the second 8-byte long in the stream.

                bool wrap = true;
                long writePosition = writingStreamDict[sensorType][f].Position;
                //check the timestamp, and re-allocate if this is too late
                writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                byte[] longBytes = new byte[8];
                writingStreamDict[sensorType][f].Read(longBytes, 0, longBytes.Length);
                long lastWraparoundTicks = BitConverter.ToInt64(longBytes, 0);
                if (lastWraparoundTicks != 0)
                {
                    DateTime lastWraparound = DateTime.FromFileTime(lastWraparoundTicks);
                    TimeSpan sinceLastWraparound = DateTime.Now.Subtract(lastWraparound);
                    if (sinceLastWraparound < f.RequiredOldness)
                    {
                        //re-allocate
                        
                        writingStreamDict[sensorType][f] = controller.ReallocateStream(sensorType, f);
                        
                        writersDict[sensorType][f] = new BinaryWriter(writingStreamDict[sensorType][f]);
                        writerStreamVersionNumbers[sensorType][f]++;
                        foreach (FeatureStream featureStream in readingStreamsDict[sensorType][f])
                        {
                            featureStream.updateStream(controller.OpenReadStream(sensorType, f));
                        }
                        //don't wrap because we just re-allocated
                        wrap = false;
                    }
                    longBytes = BitConverter.GetBytes(DateTime.Now.ToFileTime());
                    writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                    writingStreamDict[sensorType][f].Write(longBytes, 0, longBytes.Length);
                    writingStreamDict[sensorType][f].Seek(writePosition, SeekOrigin.Begin);
                }
                else
                {
                    //lastwraparound time was zero, this is the first time through
                    writingStreamDict[sensorType][f].Seek(8, SeekOrigin.Begin);
                    longBytes = BitConverter.GetBytes(DateTime.Now.ToFileTime());
                    writingStreamDict[sensorType][f].Write(longBytes, 0, longBytes.Length);
                    writingStreamDict[sensorType][f].Seek(writePosition, SeekOrigin.Begin);
                }


                if (wrap)
                    writingStreamDict[sensorType][f].Seek(FeatureStream.RESERVED_BYTES, SeekOrigin.Begin);  
                
                
                for (; ii < length; ii++)
                {
                    writersDict[sensorType][f].Write(buffer[offset + ii]);
                }
            }
            writersDict[sensorType][f].Flush();
            long position = writingStreamDict[sensorType][f].Position;
            writersDict[sensorType][f].Seek(0, SeekOrigin.Begin);
            long newWriteTotal = writeTotals[sensorType][f] + ii * sizeof(double);
            writersDict[sensorType][f].Write(newWriteTotal);
            writersDict[sensorType][f].Flush();
            writersDict[sensorType][f].BaseStream.Seek(position, SeekOrigin.Begin);
            writeTotals[sensorType][f] = newWriteTotal;
        }
        #endregion

       

        /// <summary>
        /// Tell the sensor to start calculating a particular feature.
        /// </summary>
        /// <param name="name">The name of the feature</param>
        /// <param name="minAcceptablePeriod">The minimum period (1/frequency) of 
        /// the feature that the caller is willing to accept. Must be non-zero</param>
        /// <param name="maxAcceptablePeriod">The maximum period (1/frequency) of 
        /// the feature that the caller is willing to accept. Must be non-zero</param>
        /// <returns>A FeatureStream. FeatureStreams are read-only. If the sensor 
        /// is already calculating this feature at a period that falls in the 
        /// specified range, the stream will read that feature. Otherwise,
        /// the stream will read a new feature whose period is the average
        /// of the min and max acceptable periods</returns>
        /// <exception>If either the (name,maxPeriod) or (name,minPeriod) pairs are rejected by the sensor as possible features</exception>
        /// <exception>If the requiredOldness param is less than either of the period parameters</exception>
        public FeatureStream OpenFeature(string name, TimeSpan minAcceptablePeriod, TimeSpan maxAcceptablePeriod, TimeSpan requiredOldnessParam)//,  TimeSpan callingPeriod, ReadFeatureDelegate callback)
        {
            if (!workingInstance)
                return instances[sensorType].OpenFeature(name, minAcceptablePeriod, maxAcceptablePeriod, requiredOldnessParam);//, callingPeriod, callback);
            
            if (minAcceptablePeriod == TimeSpan.Zero || maxAcceptablePeriod == TimeSpan.Zero)
                throw new Exception("A period of 0 is not valid");
            if (requiredOldnessParam < minAcceptablePeriod || requiredOldnessParam < maxAcceptablePeriod)
                throw new Exception("The requiredOldness must be higher than the period parameters");
            if (!FeatureSupported(name, minAcceptablePeriod) || !FeatureSupported(name, maxAcceptablePeriod))
                throw new Exception("Unsupported (feature,period) pair for this sensor");
            lock (featureDict[sensorType])
            {
                checkFeatureList();
                List<Feature> features = featureDict[sensorType];
                Feature matchingFeature = features.Find(delegate(Feature feature) { return ( feature.Name.Equals(name) && feature.Period >= minAcceptablePeriod && feature.Period <= maxAcceptablePeriod); } );//getFeaturePredicate(name, minAcceptablePeriod, maxAcceptablePeriod));
                if (matchingFeature == null)
                {
                    TimeSpan period = TimeSpan.FromTicks(maxAcceptablePeriod.Subtract(minAcceptablePeriod).Ticks / 2) + minAcceptablePeriod;
                    matchingFeature = new Feature(name, period, requiredOldnessParam, 0);//if this is going to be the very first one, the version number is always zero
                    
                    //also add this feature to the inter-process list of features
                    controller.WriteFeature(sensorType, matchingFeature);
                    
                    //make sure a writing stream is open
                    writingStreamDict[sensorType][matchingFeature] = controller.OpenWriteStream(sensorType, matchingFeature);
                    writersDict[sensorType][matchingFeature] = new BinaryWriter(writingStreamDict[sensorType][matchingFeature]);
                    writeTotals[sensorType][matchingFeature] = 0L;
                    writerStreamVersionNumbers[sensorType][matchingFeature] = 0;

                    //This is the true "starting" position of the data in the stream. The first 
                    //few bytes are reserved for bookkeeping.
                    writersDict[sensorType][matchingFeature].Seek(FeatureStream.RESERVED_BYTES, SeekOrigin.Begin);
                    featureDict[sensorType].Add(matchingFeature);
                }
                //if the feature already exists, check that the oldness requirement is at least as long as the new one
                if (matchingFeature.RequiredOldness < requiredOldnessParam)
                {
                    matchingFeature.RequiredOldness = requiredOldnessParam;
                    controller.WriteFeature(sensorType, matchingFeature);
                }

                //open a reading stream
                Stream readStream = controller.OpenReadStream(sensorType, matchingFeature);

                FeatureStream featureStream = new FeatureStream(readStream, matchingFeature);
                //add a reference to the reading stream
                if (!readingStreamsDict[sensorType].ContainsKey(matchingFeature))
                {
                    readingStreamsDict[sensorType][matchingFeature] = new List<FeatureStream>();
                }
                readingStreamsDict[sensorType][matchingFeature].Add(featureStream);

                return featureStream;
            }
        }


        /// <summary>
        /// Allows sensors to specify how much time should elapse between calls to
        /// calculateFeatures(). 
        /// </summary>
        /// <returns>The time between calls to calculateFeatures(), in milliseconds</returns>
        protected virtual int getSleepTimeMillis()
        {
            return 100;
        }
        #region Overridden functions

        protected abstract void CalculateFeatures(List<Feature> features);
        protected abstract void OnStart();
        protected abstract void OnStop();
        protected abstract bool FeatureSupported(string name, TimeSpan period);

        #endregion
    }
}