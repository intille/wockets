/*
 * Created By Salim Khan
 */
package edu.mit.media.wockets.Beans;

public class User {
	private int user_Id;
	private String fName;
	private String lName;
	private String email;
	private String regist_Date;
	private char activeStatus;
	private String disable_Date;
	private Account account;

	public User()
	{
		this.account = new Account();
	}
	
	public Account getAccount() {
		return account;
	}
	public void setAccount(Account account) {
		this.account = account;
	}
	public int getUser_Id() {
		return user_Id;
	}
	public void setUser_Id(int user_Id) {
		this.user_Id = user_Id;
	}
	public String getfName() {
		return fName;
	}
	public void setfName(String fName) {
		this.fName = fName;
	}
	public String getlName() {
		return lName;
	}
	public void setlName(String lName) {
		this.lName = lName;
	}
	public String getEmail() {
		return email;
	}
	public void setEmail(String email) {
		this.email = email;
	}
	public String getRegist_Date() {
		return regist_Date;
	}
	public void setRegist_Date(String regist_Date) {
		this.regist_Date = regist_Date;
	}
	public char getActiveStatus() {
		return activeStatus;
	}
	public void setActiveStatus(char activeStatus) {
		this.activeStatus = activeStatus;
	}
	public String getDisable_Date() {
		return disable_Date;
	}
	public void setDisable_Date(String disable_Date) {
		this.disable_Date = disable_Date;
	}
	
}
