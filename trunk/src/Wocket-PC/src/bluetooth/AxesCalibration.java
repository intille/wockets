package bluetooth;

/**
 *
 * @author Aida
 */
public class AxesCalibration {
    private int noise;
    private int mid;
    private int negativeMid;
    private int min;
    private int max;

    public int getMax() {
        return max;
    }

    public void setMax(int max) {
        this.max = max;
    }

    public int getMid() {
        return mid;
    }

    public void setMid(int mid) {
        this.mid = mid;
    }

    public int getMin() {
        return min;
    }

    public void setMin(int min) {
        this.min = min;
    }

    public int getNegativeMid() {
        return negativeMid;
    }

    public void setNegativeMid(int negativeMid) {
        this.negativeMid = negativeMid;
    }

    public int getNoise() {
        return noise;
    }

    public void setNoise(int noise) {
        this.noise = noise;
    }
        
}
