/*
 * Created By Salim Khan
 * Account Bean for Account object
 */

package edu.mit.media.wockets.Beans;

public class Account {
	private String userName;
	private String pwd;
	private String role;
    private String re_pwd;
    
    
	public String getRe_pwd() {
		return re_pwd;
	}
	public void setRe_pwd(String re_pwd) {
		this.re_pwd = re_pwd;
	}
	public String getUserName() {
		return userName;
	}
	public void setUserName(String userName) {
		this.userName = userName;
	}
	public String getPwd() {
		return pwd;
	}
	public void setPwd(String pwd) {
		this.pwd = pwd;
	}
	public String getRole() {
		return role;
	}
	public void setRole(String role) {
		this.role = role;
	}
	
	

}
