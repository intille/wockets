package bluetooth;

import java.util.Date;

public class SamplingRate {
	public long total_time = 0;
	public int counter = 0;
	public Date prev_time = new Date();
	public double samplingRate = 0;
    public int flag = 0;
}
