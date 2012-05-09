package UserInterface;

import com.intel.bluetooth.BlueCoveImpl;
import java.awt.CardLayout;
import java.io.IOException;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.microedition.io.StreamConnection;
import javax.swing.JOptionPane;
import javax.swing.JPanel;

/**
 *
 * @author Aida
 */
public class CalibrationPanel extends javax.swing.JPanel {
    
    JPanel userProcessContainer;
    StreamConnection streamConnection;
    
    public CalibrationPanel(JPanel upc, StreamConnection sc) throws IOException{
        initComponents();
        userProcessContainer = upc;
        streamConnection = sc; 
    }
    
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        calibrateButton = new javax.swing.JButton();
        jLabel3 = new javax.swing.JLabel();
        jLabel1 = new javax.swing.JLabel();
        SamplingRateTextField = new javax.swing.JTextField();
        jLabel2 = new javax.swing.JLabel();
        jLabel4 = new javax.swing.JLabel();

        calibrateButton.setText("Calibrate The Wocket ");
        calibrateButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                calibrateButtonActionPerformed(evt);
            }
        });

        jLabel3.setFont(new java.awt.Font("Tahoma", 0, 14)); // NOI18N
        jLabel3.setText("Calibrating the Wocket");

        jLabel1.setFont(new java.awt.Font("Tahoma", 0, 18)); // NOI18N
        jLabel1.setText("PC-Wocket Application");

        jLabel2.setText("Favorite Sampling Rate:");

        jLabel4.setText("You are now connected to the Wocket. Select the favorite sampling rate:");

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
                                .addComponent(jLabel3))
                            .addGroup(layout.createSequentialGroup()
                                .addGap(20, 20, 20)
                                .addComponent(calibrateButton))
                            .addGroup(layout.createSequentialGroup()
                                .addComponent(jLabel2)
                                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.UNRELATED)
                                .addComponent(SamplingRateTextField, javax.swing.GroupLayout.PREFERRED_SIZE, 55, javax.swing.GroupLayout.PREFERRED_SIZE))))
                    .addGroup(layout.createSequentialGroup()
                        .addContainerGap()
                        .addComponent(jLabel4)))
                .addContainerGap(49, Short.MAX_VALUE))
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
                .addGap(18, 18, 18)
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
                    .addComponent(SamplingRateTextField, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
                    .addComponent(jLabel2))
                .addGap(18, 18, 18)
                .addComponent(calibrateButton)
                .addGap(94, 94, 94))
        );
    }// </editor-fold>//GEN-END:initComponents

    private void calibrateButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_calibrateButtonActionPerformed
        String temp = SamplingRateTextField.getText();
        if (temp == null){
            JOptionPane.showMessageDialog(null, "Please select the Sampling Rate!");
            return;
        }
        int samplingRate = Integer.parseInt(temp);
        JOptionPane.showMessageDialog(null, "It may take 3-10 minutes!");
        JPanel calProcessPanel = null;
        try {
            calProcessPanel = new CalProcessPanel(userProcessContainer, streamConnection, samplingRate);
        } catch (Exception ex) {
            Logger.getLogger(CalibrationPanel.class.getName()).log(Level.SEVERE, null, ex);
        }
        userProcessContainer.add("CalProcessPanel",calProcessPanel);
        CardLayout c1 = (CardLayout)userProcessContainer.getLayout();
        c1.next(userProcessContainer);
    }//GEN-LAST:event_calibrateButtonActionPerformed
   
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
    private javax.swing.JButton calibrateButton;
    private javax.swing.JLabel jLabel1;
    private javax.swing.JLabel jLabel2;
    private javax.swing.JLabel jLabel3;
    private javax.swing.JLabel jLabel4;
    // End of variables declaration//GEN-END:variables
}
