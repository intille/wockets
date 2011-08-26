using System;

namespace HousenCS.MITes
{
	/// <summary>
	/// Summary description for MITesActivityCounter.
	/// </summary>
	public class MITesDemoObjectAnalyzer
	{
		private MITesDecoder aMITesDecoder;

		private int[] objectsSeen = new int[300];
		private int[] objectsVals = new int[300];
		private int[] objectsReps = new int[300];
		private int numObjectsSeen = 0;  

		/// <summary>
		/// 
		/// </summary>
		/// <param name="aMITesDecoder"></param>
		public MITesDemoObjectAnalyzer(MITesDecoder aMITesDecoder)
		{
			this.aMITesDecoder = aMITesDecoder;
		}

		private void Warning(String aMsg)
		{
			Console.WriteLine("WARNING: " + aMsg);
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public int[] GetIDs()
		{
			return objectsSeen;
		}
		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public int[] GetVals()
		{
			return objectsVals;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public int[] GetReps()
		{
			return objectsReps;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <returns></returns>
		public int GetNumIDs()
		{
			return numObjectsSeen;
		}

		private void AddObject(int id, int val, int rep)
		{
			for (int i = 0; i < numObjectsSeen; i++)
				if (objectsSeen[i] == id)
				{
					objectsVals[i] = val;
					objectsReps[i] = rep;
					return;
				}

			// Didn't find it, so add
			objectsSeen[numObjectsSeen] = id;
			objectsVals[numObjectsSeen] = val;
			objectsReps[numObjectsSeen] = rep;
			numObjectsSeen++;
		}

		private bool IsSeen(int id)
		{
			for (int i = 0; i < numObjectsSeen; i++)
				if (objectsSeen[i] == id)
					return true;
			return false;
		}

		private void Clear()
		{
			numObjectsSeen = 0;
		}

		/// <summary>
		/// Grab and store the latest object values from the MITesDecoder data stream.
		/// </summary>
		public void Update()
		{
			Clear();
			for (int i = 0; i < aMITesDecoder.someMITesDataIndex; i++)
			{
				if (aMITesDecoder.someMITesData[i].type == (int) MITesTypes.STATIC)
				{
					//					if ((ID == MITesData.NONE) ||
					//						(aMITesDecoder.someMITesData[i].id == ID))
					//					{
					int id = aMITesDecoder.someMITesData[i].id;
					int val = aMITesDecoder.someMITesData[i].sensorValue;
					int rep = aMITesDecoder.someMITesData[i].recentActivationsValue;
					bool alive = aMITesDecoder.someMITesData[i].isAlive;
					Console.WriteLine("-----------> OBJECT: " + id + " " + val + " " + rep + " " + alive);
					if (alive)
						val = -1;
					AddObject(id, val, rep); 
				}			
			}
		}
	}
}