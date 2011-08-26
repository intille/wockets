/**
 * 
 */
package com.everyfit.wockets.exceptions;

/**
 * @author albinali
 *
 */
public abstract class WocketException extends Exception {

	public String _Method="";
	public String _StackTrace="";
	public String _Message="";
	/**
	 * 
	 */
	public WocketException(String method,String stack,String message) {
		// TODO Auto-generated constructor stub
		this._Method=method;
		this._StackTrace=stack;
		this._Message=message;
	}

	@Override
	public String toString(){
		return "Method:"+this._Method+",Message:"+this._Message+",StackTrace:"+this._StackTrace;
	}
}
