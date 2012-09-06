package wockets.data;

/**
 *
 * @author Aida
 */
public class ParticipantData {
   private String pID;
   private String rwMAC;
   private String raMAC; 
   private String gwMAC;
   private String gaMAC;

    public String getGaMAC() {
        return gaMAC;
    }

    public void setGaMAC(String gaMAC) {
        this.gaMAC = gaMAC;
    }

    public String getGwMAC() {
        return gwMAC;
    }

    public void setGwMAC(String gwMAC) {
        this.gwMAC = gwMAC;
    }

    public String getpID() {
        return pID;
    }

    public void setpID(String pID) {
        this.pID = pID;
    }

    public String getRaMAC() {
        return raMAC;
    }

    public void setRaMAC(String raMAC) {
        this.raMAC = raMAC;
    }

    public String getRwMAC() {
        return rwMAC;
    }

    public void setRwMAC(String rwMAC) {
        this.rwMAC = rwMAC;
    }
   
   
}
