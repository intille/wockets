using System;
using System.Collections.Generic;
using System.Text;
using System.Collections;

namespace WocketsWeka.Utils.DTs
{
    public class FeatureSelector
    {
        
        public static Hashtable ClusterByOrientations(int[][] orientations)
        {
            //identify the columns with 0 orientations / can be any orientation
            bool[] ignoreColumn = new bool[orientations[0].Length];
            int radix = 0;
            for (int j = 0; (j < ignoreColumn.Length); j++)
            {
                ignoreColumn[j] = false;
                for (int i = 0; (i < orientations.Length); i++)
                {
                    if (orientations[i][j] > radix)
                        radix = orientations[i][j];

                    if (orientations[i][j] == 0)
                    {
                        ignoreColumn[j] = true;
                        break;
                    }
                }
            }

            Hashtable clusters = new Hashtable();
            
            //each cluster will be assigned a unique id number in a way similar to
            // converting binary numbers to decimal, a radix is detemined based
            // on the largest orientation number (i.e. number of pictures)
            // then an id is calculated as follows first body part x radix ^0  + second body part x radix ^1
            // etc.
            radix++;

            for (int i = 0; (i < orientations.Length); i++)
            {
                int key = 0;
                for (int j = 0; (j < orientations[0].Length); j++)
                    if (ignoreColumn[j] ==false)
                        key += orientations[i][j]*(int)Math.Pow(radix,j);
                if (clusters.Contains(key) == false)
                {
                    ArrayList oneCluster = new ArrayList();
                    clusters[key] = oneCluster;
                }                                
                ((ArrayList)clusters[key]).Add(i);
            }

            return clusters;
        }


        public static Hashtable GetFeaturesByMobility(Hashtable clusters, int[][] mobilityMatrix)
        {
            Hashtable mobilityFeatures = new Hashtable();
            foreach (DictionaryEntry entry in clusters)
            {
                int cluster_id = (int) entry.Key;
                ArrayList cluster = (ArrayList)entry.Value;
                ArrayList clusterFeatures = new ArrayList();
                if (cluster.Count > 1) // pick features only if the cluster has more than 1 member
                {
                    for (int j = 0; (j < mobilityMatrix[0].Length); j++)
                    {
                        bool sameMobility = false;
                        for (int x = 0; (x < cluster.Count); x++)
                            for (int y = x + 1; (y < cluster.Count); y++)
                                if (mobilityMatrix[(int)cluster[x]][j] == mobilityMatrix[(int)cluster[y]][j])
                                    sameMobility = true;
                        if (sameMobility == false)
                            clusterFeatures.Add(j);
                    }
                }
                mobilityFeatures[cluster_id] = clusterFeatures;
            }

            return mobilityFeatures;
        }
    }
}
