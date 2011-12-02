/*Created By Salim Khan
 * Email Utility class for email functionality
 * It also has attachement feature but it is disable
 */
package edu.mit.media.wockets.utility;

import javax.mail.MessagingException;
import javax.mail.internet.MimeMessage;

import org.springframework.core.io.FileSystemResource;
import org.springframework.mail.MailParseException;
import org.springframework.mail.SimpleMailMessage;
import org.springframework.mail.javamail.JavaMailSender;
import org.springframework.mail.javamail.MimeMessageHelper;

public class Mail {
	
	private JavaMailSender mailSender;
	private SimpleMailMessage simpleMailMessage;
	
	
   public void setSimpleMailMessage(SimpleMailMessage simpleMailMessage) {
		this.simpleMailMessage = simpleMailMessage;
	}
	
	public void setMailSender(JavaMailSender mailSender) {
		this.mailSender = mailSender;
	}
	
	
	public JavaMailSender getMailSender(){
		return this.mailSender;
	}
	
	public SimpleMailMessage getSimpleMailMessage(){
		return this.simpleMailMessage;
	}

	//public void sendMail(String dear, String content,String fileName,String to,String subject) {
	public void sendMail(String dear, String content,String to,String subject) {
		 
		   MimeMessage message = mailSender.createMimeMessage();
	 
		   try{
			MimeMessageHelper helper = new MimeMessageHelper(message, true);
	 
			helper.setFrom(simpleMailMessage.getFrom());
			helper.setTo(to);
			helper.setSubject(subject);
			helper.setText(String.format(
				simpleMailMessage.getText(), dear, content));
	 
//			FileSystemResource file = new FileSystemResource(fileName);
//			helper.addAttachment(file.getFilename(), file);
	 
		     }catch (MessagingException e) {
			throw new MailParseException(e);
		     }
		     mailSender.send(message);
	         }

}
