package UserInterface;

import DataCollection.WocketDecoder;
import bluetooth.CalibrationValues;
import bluetooth.PcClient;
import bluetooth.WocketParam;
import com.intel.bluetooth.BlueCoveImpl;
import java.awt.CardLayout;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.microedition.io.StreamConnection;
import javax.swing.*;
import  sun.audio.*;
import  java.io.*;

/**
 *
 * @author Aida
 */
public class SetSamplingRate extends javax.swing.JPanel {
    
    JPanel userProcessContainer;
    StreamConnection streamConnection;
    InputStream inStream = null;
    OutputStream outStream = null;
    CalibrationValues calibrationValues;
    
    public SetSamplingRate(JPanel upc, StreamConnection sc, CalibrationValues cvalues) throws IOException{
        initComponents();
        userProcessContainer = upc;
        streamConnection = sc; 
        outStream = streamConnection.openOutputStream();
        outStream.write(PcClient.WOCKET_Continuous_PACKET);
        inStream = streamConnection.openInputStream();
        continueButton.setVisible(false);
        calibrationValues = cvalues;
    }
    
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        samplingRateButton = new javax.swing.JButton();
        jLabel3 = new javax.swing.JLabel();
        jLabel1 = new javax.swing.JLabel();
        SamplingRateTextField = new javax.swing.JTextField();
        jLabel2 = new javax.swing.JLabel();
        jLabel4 = new javax.swing.JLabel();
        backButton = new javax.swing.JButton();
        continueButton = new javax.swing.JButton();
        skipButton = new javax.swing.JButton();
        messageLabel = new javax.swing.JLabel();

        samplingRateButton.setText("Set Sampling Rate");
        samplingRateButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                samplingRateButtonActionPerformed(evt);
            }
        });

        jLabel3.setFont(new java.awt.Font("Tahoma", 0, 14)); // NOI18N
        jLabel3.setText("Set Sampling rate");

        jLabel1.setFont(new java.awt.Font("Tahoma", 0, 18)); // NOI18N
        jLabel1.setText("PC-Wocket Application");

        jLabel2.setText("Target Sampling Rate:");

        jLabel4.setText("Wockets are now connected. Select the target sampling rate:");

        backButton.setText("Back");
        backButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                backButtonActionPerformed(evt);
            }
        });

        continueButton.setText("Continue");
        continueButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                continueButtonActionPerformed(evt);
            }
        });

        skipButton.setText("Skip Sampling rate Calibration");
        skipButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                skipButtonActionPerformed(evt);
            }
        });

        messageLabel.setFont(new java.awt.Font("Tahoma", 1, 12)); // NOI18N
        messageLabel.setText(" ");

        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(this);
        this.setLayout(layout);
        layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addGroup(layout.createSequentialGroup()
                        .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                            .addGroup(layout.createSequentialGroup()
                                .addGap(110, 110, 110)
                                .addComponent(jLabel1))
                            .addGroup(layout.createSequentialGroup()
                                .addGap(142, 142, 142)
                                .addComponent(jLabel3))
                            .addGroup(layout.createSequentialGroup()
                                .addGap(47, 47, 47)
                                .addComponent(jLabel4))
                            .addGroup(layout.createSequentialGroup()
                                .addGap(107, 107, 107)
                                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                                    .addGroup(layout.createSequentialGroup()
                                        .addComponent(jLabel2)
                                        .addGap(18, 18, 18)
                                        .addComponent(SamplingRateTextField, javax.swing.GroupLayout.PREFERRED_SIZE, 55, javax.swing.GroupLayout.PREFERRED_SIZE))
                                    .addGroup(layout.createSequentialGroup()
                                        .addGap(41, 41, 41)
                                        .addComponent(samplingRateButton))))
                            .addGroup(layout.createSequentialGroup()
                                .addComponent(backButton)
                                .addGap(49, 49, 49)
                                .addComponent(skipButton)))
                        .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED, 6, Short.MAX_VALUE)
                        .addComponent(continueButton))
                    .addGroup(layout.createSequentialGroup()
                        .addGap(57, 57, 57)
                        .addComponent(messageLabel, javax.swing.GroupLayout.PREFERRED_SIZE, 319, javax.swing.GroupLayout.PREFERRED_SIZE)
                        .addGap(0, 0, Short.MAX_VALUE)))
                .addContainerGap())
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addGap(19, 19, 19)
                .addComponent(jLabel1)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.UNRELATED)
                .addComponent(jLabel3)
                .addGap(13, 13, 13)
                .addComponent(jLabel4, javax.swing.GroupLayout.PREFERRED_SIZE, 23, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addGap(18, 18, 18)
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addComponent(SamplingRateTextField, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
                    .addComponent(jLabel2))
                .addGap(18, 18, 18)
                .addComponent(samplingRateButton)
                .addGap(40, 40, 40)
                .addComponent(messageLabel)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED, 121, Short.MAX_VALUE)
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
                    .addComponent(backButton)
                    .addComponent(continueButton)
                    .addComponent(skipButton)))
        );
    }// </editor-fold>//GEN-END:initComponents

    private void samplingRateButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_samplingRateButtonActionPerformed
        skipButton.setVisible(false);
        samplingRateButton.disable();
        /*String temp = SamplingRateTextField.getText();
        if (temp == null){
            JOptionPane.showMessageDialog(null, "Please select the Sampling Rate!");
            return;
        }
        int samplingRate = Integer.parseInt(temp);
        calibrationValues.setSamplingRate(samplingRate);*/
        messageLabel.setText("It may take 3-10 minutes. You will hear a Beep sound \n when the sampling rate is set.");
        //JOptionPane.showMessageDialog(null, "It may take 3-10 minutes!");
        
        /*final Runnable beepRunnable = new Runnable() {
            public void run() { 
                try { 
                    InputStream in= new FileInputStream("src/rsc/beep.wav");
                    AudioStream as = new AudioStream(in);  
                    AudioPlayer.player.start(as);  
                    //AudioPlayer.player.stop(as); 
                } catch (IOException ex) {
                    Logger.getLogger(SetSamplingRatePanel.class.getName()).log(Level.SEVERE, null, ex);
                } 
            }            
        };*/

        Runnable setSRRunnable = new Runnable() {
            public void run() { 
                try {                     
                    String temp = SamplingRateTextField.getText();
                    if (temp == null){
                        JOptionPane.showMessageDialog(null, "Please select the Sampling Rate!");
                        return;
                    }
                    int samplingRate = Integer.parseInt(temp);
                    calibrationValues.setSamplingRate(samplingRate);
                    PcClient.Calibrate_SamplingRate(samplingRate, inStream, outStream, messageLabel); 
                    messageLabel.setText("Calibrating the Sampling Rate is done.");        
                    continueButton.setVisible(true);
                    PcClient.beepRunnable.run();
                } catch (IOException ex) {
                    Logger.getLogger(SetSamplingRate.class.getName()).log(Level.SEVERE, null, ex);
                } 
            }            
        };
        SwingUtilities.invokeLater(setSRRunnable);         
        
          
        //jTextArea.setText("Calibrating the Sampling Rate is done.");        
        //continueButton.setVisible(true);
        //JOptionPane.showMessageDialog(null, "Sampling Rate is set.");
        
        
        
        /*JTextArea textArea = new JTextArea();
        final JProgressBar progressBar = new JProgressBar(0, 100);
        PrimeNumbersTask task = new PrimeNumbersTask(textArea, N);
        task.addPropertyChangeListener(
            new PropertyChangeListener() {
                public  void propertyChange(PropertyChangeEvent evt) {
                    if ("progress".equals(evt.getPropertyName())) {
                        progressBar.setValue((Integer)evt.getNewValue());
                    }
                }
            });
        //task.execute();
        SwingUtilities.invokeLater(task);*/
    }//GEN-LAST:event_samplingRateButtonActionPerformed

    
    
    private void backButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_backButtonActionPerformed
        try {
            streamConnection.close();
            PcClient.stop();            
        } catch (IOException ex) {
            Logger.getLogger(SetSamplingRate.class.getName()).log(Level.SEVERE, null, ex);
        }
        userProcessContainer.removeAll();        
        JPanel startPanel =  new StartPanel(userProcessContainer);
        userProcessContainer.add("StartPanel",startPanel);
        CardLayout c1 = (CardLayout)userProcessContainer.getLayout();
        c1.next(userProcessContainer);        
    }//GEN-LAST:event_backButtonActionPerformed

    private void continueButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_continueButtonActionPerformed
        //JPanel noiseCalibrationPanel = new MeasureNoise(userProcessContainer, inStream, outStream);
        //userProcessContainer.add("noiseCalibrationPanel",noiseCalibrationPanel);
        JPanel calibrateXPanel= null;
        try {
            calibrateXPanel = new MeasureXAxis(userProcessContainer, inStream, outStream, calibrationValues);
        } catch (IOException ex) {
            Logger.getLogger(SetSamplingRate.class.getName()).log(Level.SEVERE, null, ex);
        }
        userProcessContainer.add("calibrateXPanel",calibrateXPanel);
        CardLayout c1 = (CardLayout)userProcessContainer.getLayout();
        c1.next(userProcessContainer);
    }//GEN-LAST:event_continueButtonActionPerformed

    private void skipButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_skipButtonActionPerformed
        JPanel calibrateXPanel= null;
        try {
            calibrateXPanel = new MeasureXAxis(userProcessContainer, inStream, outStream, calibrationValues);
        } catch (IOException ex) {
            Logger.getLogger(SetSamplingRate.class.getName()).log(Level.SEVERE, null, ex);
        }
        userProcessContainer.add("calibrateXPanel",calibrateXPanel);
        CardLayout c1 = (CardLayout)userProcessContainer.getLayout();
        c1.next(userProcessContainer);
    }//GEN-LAST:event_skipButtonActionPerformed
   
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
    private javax.swing.JTextField SamplingRateTextField;
    private javax.swing.JButton backButton;
    private javax.swing.JButton continueButton;
    private javax.swing.JLabel jLabel1;
    private javax.swing.JLabel jLabel2;
    private javax.swing.JLabel jLabel3;
    private javax.swing.JLabel jLabel4;
    private javax.swing.JLabel messageLabel;
    private javax.swing.JButton samplingRateButton;
    private javax.swing.JButton skipButton;
    // End of variables declaration//GEN-END:variables
}
