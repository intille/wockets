/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package UserInterface;

import bluetooth.PcClient;
import com.intel.bluetooth.BlueCoveImpl;
import java.awt.CardLayout;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.microedition.io.StreamConnection;
import javax.swing.JOptionPane;
import javax.swing.JPanel;

/**
 *
 * @author Aida
 */
public class CalProcessPanel extends javax.swing.JPanel {

    byte[] WOCKET_Continuous_PACKET = {(byte) 0xBA, (byte)0x00};
    
    JPanel userProcessContainer;
    int samplingRate;
    StreamConnection streamConnection;
    InputStream inStream = null;
    OutputStream outStream = null;
    
    public CalProcessPanel(JPanel upc, StreamConnection sc, int sr) throws Exception{
        initComponents();
        userProcessContainer = upc;
        streamConnection = sc;
        samplingRate = sr;
        
        //write
        outStream = streamConnection.openOutputStream();
        outStream.write(WOCKET_Continuous_PACKET);
        
        //read		
        inStream = streamConnection.openInputStream();
        
        try {
            PcClient.Calibrate_SamplingRate(samplingRate, inStream, outStream);            
        } catch (IOException ex) {
            Logger.getLogger(CalibrationPanel.class.getName()).log(Level.SEVERE, null, ex);
        }
        messageTextField.setText("Calibration Procedure is finished");
        JOptionPane.showMessageDialog(null, "Calibration Procedure is finished.");
    }

    
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        jScrollPane2 = new javax.swing.JScrollPane();
        jTextArea1 = new javax.swing.JTextArea();
        jLabel3 = new javax.swing.JLabel();
        jLabel1 = new javax.swing.JLabel();
        jLabel4 = new javax.swing.JLabel();
        messageTextField = new javax.swing.JTextField();

        jTextArea1.setColumns(20);
        jTextArea1.setRows(5);
        jScrollPane2.setViewportView(jTextArea1);

        jLabel3.setFont(new java.awt.Font("Tahoma", 0, 14)); // NOI18N
        jLabel3.setText("Calibrating the Wocket");

        jLabel1.setFont(new java.awt.Font("Tahoma", 0, 18)); // NOI18N
        jLabel1.setText("PC-Wocket Application");

        jLabel4.setText("Calibrating a Wocket may takes 6-10 minutes.");

        messageTextField.setText("   ");

        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(this);
        this.setLayout(layout);
        layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addGroup(layout.createSequentialGroup()
                        .addGap(110, 110, 110)
                        .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                            .addComponent(jLabel1)
                            .addGroup(layout.createSequentialGroup()
                                .addGap(18, 18, 18)
                                .addComponent(jLabel3))))
                    .addGroup(layout.createSequentialGroup()
                        .addGap(91, 91, 91)
                        .addComponent(jLabel4))
                    .addGroup(layout.createSequentialGroup()
                        .addGap(53, 53, 53)
                        .addComponent(messageTextField, javax.swing.GroupLayout.PREFERRED_SIZE, 283, javax.swing.GroupLayout.PREFERRED_SIZE)))
                .addContainerGap(74, Short.MAX_VALUE))
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addGap(19, 19, 19)
                .addComponent(jLabel1)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.UNRELATED)
                .addComponent(jLabel3)
                .addGap(18, 18, 18)
                .addComponent(jLabel4, javax.swing.GroupLayout.DEFAULT_SIZE, 40, Short.MAX_VALUE)
                .addGap(39, 39, 39)
                .addComponent(messageTextField, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addGap(114, 114, 114))
        );
    }// </editor-fold>//GEN-END:initComponents
    @Override
    protected void finalize() throws Throwable {
        try {
            streamConnection.close();
            BlueCoveImpl.shutdown();
        } finally {
            super.finalize();
        }
    }  
        
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JLabel jLabel1;
    private javax.swing.JLabel jLabel3;
    private javax.swing.JLabel jLabel4;
    private javax.swing.JScrollPane jScrollPane2;
    private javax.swing.JTextArea jTextArea1;
    private javax.swing.JTextField messageTextField;
    // End of variables declaration//GEN-END:variables
}
