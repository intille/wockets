package decoding;


public class ConvertData 
{
	private byte[] data;
	private static int previousX=0, previousY=0, previousZ=0;
	private static int posiCheck=0;
	private final static int maxNoSignals=2400;
	
	public byte[] encoData(int xCoords, int yCoords, int zCoords)
	{
		int check=0;
		byte[] finalData = null;
		int dx,dy,dz;
		dx=xCoords-previousX;
		dy=yCoords-previousY;
		dz=zCoords-previousZ;
		previousX=xCoords;
		previousY=yCoords;
		previousZ=zCoords;
		if(posiCheck==maxNoSignals)
		{
			posiCheck=0;
		}
		posiCheck++;
		
		if(posiCheck==1)
		{
			finalData=this.uncompressedData(xCoords, yCoords, zCoords);
			return finalData;
		}
		
		
		if (check==0)
			if(dx>=-15 && dx<=15)
				if(dy>=-15 && dy<=15)
					if(dz>=-15 && dz<=15)
						check=1;
			
		if (check==1)
		{
			finalData=this.compressedData(dx,dy,dz);
		}
		
		else 
		{
			finalData=this.uncompressedData(xCoords, yCoords, zCoords);
		}
		return finalData;
	}

	
	byte[] compressedData(int dx, int dy, int dz)
	{
		data = new byte[2];
		initPacket(data.length);
		
		int[] minusCheck=new int[3];
		minusCheck[0]=dx;
		minusCheck[1]=dy;
		minusCheck[2]=dz;
		
		for(int i=0;i<3;i++)
		{
			if(minusCheck[i]<0)
			{
				minusCheck[i]*=-1;
				minusCheck[i]|=0x10;
			}
		}
		
		byte tempY;
		
		data[0]=(byte) (minusCheck[0]<<2);
		
		tempY=(byte) (minusCheck[1]>>3); 
		data[0]=(byte) (data[0]|tempY);
		
		data[1]=(byte) (minusCheck[1]<<5);
		data[1]=(byte) (data[1]|minusCheck[2]);
		return data;
	}
	
	byte[] uncompressedData(int x, int y, int z)
	{
		data = new byte[4];
		initPacket(data.length);
		
		byte tempX, tempY, tempZ;
		tempX= 	(byte) (x>>4);
		data[0]=(byte) (data[0]|tempX);
		data[0]=(byte) (data[0]|0xC0);
		
		tempX= 	(byte) (x<<4);
		tempY=	(byte) (y>>6);
		data[1]=(byte) (data[1]|tempY);
		data[1]=(byte) (data[1]|tempX);
		
		tempY= 	(byte) (y<<2);
		tempZ= 	(byte) (z>>8);
		data[2]=(byte) (data[2]|tempZ);
		data[2]=(byte) (data[2]|tempY);
		
		data[3]=(byte) (z);
		return data;
	}
	
	void initPacket(int length)
	{
		
		byte b=(byte)0;
		for(int i=0;i<length;i++)
		{
			data[i]=b;
		}
		
		
	}

}
