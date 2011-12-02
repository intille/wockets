/*
 * Created By Salim Khan
 * Utility to get Data Session for Hibernate
 * and to close session
 */
package edu.mit.media.wockets.utility;
import org.hibernate.Session;
import org.hibernate.SessionFactory;
import org.hibernate.cfg.Configuration;

public class HibernateSession {

	public static Session getSession(){
		Configuration config = new Configuration().configure();
		SessionFactory factory = config.buildSessionFactory();
		Session session = factory.openSession();

		return session;
	}
	
	public static void sessionClose(Session session)
	{
		session.flush();
		session.clear();
		session.close();
	}

}
