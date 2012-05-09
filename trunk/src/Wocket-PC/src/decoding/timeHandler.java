package decoding;

import java.util.Calendar;

public class timeHandler 
{

	private static Calendar prevTime=null;

	public Object timeCalc(Calendar stamp)
	{

		int timer=this.Stamper(stamp);

		if(timer==-1)
			return stamp;
		else 
			return timer;

	}

	public int Stamper(Calendar stamp)
	{
		int year, month, dayMonth = 0;
		int difference=0, check=0;
		year=stamp.get(Calendar.YEAR);
		month=stamp.get(Calendar.MONTH);
		dayMonth=stamp.get(Calendar.DAY_OF_MONTH );
		//milliSecs=stamp.get(Calendar.MILLISECOND)+(((((Calendar.HOUR_OF_DAY)*60)+Calendar.MINUTE)*60)+Calendar.SECOND)*1000;
		if (prevTime==null)
		{}	
		else{
			if(year==prevTime.get(Calendar.YEAR))
				if(month==prevTime.get(Calendar.MONTH))
					if (dayMonth==prevTime.get(Calendar.DAY_OF_MONTH ))
						check=1;


			if (check==1)
			{
				difference=(int) (stamp.getTimeInMillis()-prevTime.getTimeInMillis());
				if(difference<=255)
				{
					prevTime=stamp;
					return difference;
				}

			}}

		prevTime=stamp;
		return -1;


	}



}
