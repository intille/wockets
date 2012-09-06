package UserInterface;

import bluetooth.PcClient;
import java.awt.CardLayout;
import java.awt.event.ComponentEvent;
import java.awt.event.ComponentListener;
import java.io.IOException;
import java.util.Vector;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.bluetooth.RemoteDevice;
import javax.swing.*;
import wockets.data.ParticipantData;

/**
 *
 * @author Aida
 */
public class RunPanel extends javax.swing.JPanel {

    JPanel userProcessContainer;
    ParticipantData pData;
    Vector btDevices;
    RemoteDevice[] rRemoteDevice =  new RemoteDevice[2];
    RemoteDevice[] gRemoteDevice =  new RemoteDevice[2];
    
    public RunPanel(JPanel upc, ParticipantData pd) {
        initComponents();
        userProcessContainer = upc;
        pData = pd;
        redWocketsButton.setVisible(false);
        greenWocketsButton.setVisible(false); 
        
        this.addComponentListener(new ComponentListener() {

            @Override
            public void componentResized(ComponentEvent e) {
            }

            @Override
            public void componentMoved(ComponentEvent e) {
            }

            @Override
            public void componentShown(ComponentEvent e) {
                System.out.println("Shown");
                
                new SwingWorker<String, Object>() {
                    @Override
                    public String doInBackground() {
                        findRunnable.run(); 
                        return "";
                    }
                }.execute();
                
                //SwingWorker.invokeLater(connectRunnable);
            }

            @Override
            public void componentHidden(ComponentEvent e) {
            }
        });
        
        //SwingUtilities.invokeLater(findRunnable);
    }

    
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        jLabel1 = new javax.swing.JLabel();
        jLabel3 = new javax.swing.JLabel();
        redWocketsButton = new javax.swing.JButton();
        greenWocketsButton = new javax.swing.JButton();
        jLabel2 = new javax.swing.JLabel();
        jLabel4 = new javax.swing.JLabel();

        jLabel1.setFont(new java.awt.Font("Tahoma", 0, 18)); // NOI18N
        jLabel1.setText("PC-Wocket Application");

        jLabel3.setFont(new java.awt.Font("Tahoma", 0, 14)); // NOI18N
        jLabel3.setText("Data Collection");

        redWocketsButton.setText("Use Red Wockets  ");
        redWocketsButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                redWocketsButtonActionPerformed(evt);
            }
        });

        greenWocketsButton.setText("Use Green Wockets");
        greenWocketsButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                greenWocketsButtonActionPerformed(evt);
            }
        });

        jLabel2.setText("Searching for Wockets..");

        jLabel4.setText("      ");

        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(this);
        this.setLayout(layout);
        layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addGroup(layout.createSequentialGroup()
                        .addGap(50, 50, 50)
                        .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                            .addComponent(jLabel4)
                            .addComponent(jLabel2)))
                    .addGroup(layout.createSequentialGroup()
                        .addGap(109, 109, 109)
                        .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.TRAILING)
                            .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                                .addComponent(greenWocketsButton)
                                .addComponent(redWocketsButton))
                            .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                                .addComponent(jLabel1)
                                .addGroup(layout.createSequentialGroup()
                                    .addGap(44, 44, 44)
                                    .addComponent(jLabel3))))))
                .addContainerGap(99, Short.MAX_VALUE))
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addContainerGap()
                .addComponent(jLabel1)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.UNRELATED)
                .addComponent(jLabel3)
                .addGap(34, 34, 34)
                .addComponent(jLabel2)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(jLabel4)
                .addGap(18, 18, 18)
                .addComponent(redWocketsButton)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(greenWocketsButton)
                .addContainerGap(101, Short.MAX_VALUE))
        );
    }// </editor-fold>//GEN-END:initComponents

    private void redWocketsButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_redWocketsButtonActionPerformed
        greenWocketsButton.setVisible(false);        
        JPanel connectingPanel =  new ConnectingPanel(userProcessContainer, rRemoteDevice);
        userProcessContainer.add("ConnectingPanel",connectingPanel);
        CardLayout c1 = (CardLayout)userProcessContainer.getLayout();
        c1.next(userProcessContainer);
    }//GEN-LAST:event_redWocketsButtonActionPerformed

    private void greenWocketsButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_greenWocketsButtonActionPerformed
        redWocketsButton.setVisible(false);
        JPanel connectingPanel =  new ConnectingPanel(userProcessContainer, gRemoteDevice);
        userProcessContainer.add("ConnectingPanel",connectingPanel);
        CardLayout c1 = (CardLayout)userProcessContainer.getLayout();
        c1.next(userProcessContainer);
        
    }//GEN-LAST:event_greenWocketsButtonActionPerformed

    Runnable findRunnable = new Runnable() {
        public void run() { 
            try {
                PcClient.findDevices();                    
                Vector btDevices = PcClient.vecDevices;
                int btSize = btDevices.size();
                int rCounter = 0;
                int gCounter = 0;
                for (int k=0; k<btSize; k++){
                    RemoteDevice remoteDevice = (RemoteDevice)btDevices.elementAt(k);
                    String adr= remoteDevice.getBluetoothAddress();            
                    if (adr.contains("0006660")){
                        if ( (adr.equals(pData.getRaMAC())) || (adr.equals(pData.getRwMAC())) ){                            
                            rRemoteDevice[rCounter] = remoteDevice;
                            rCounter++;
                            System.out.println(adr);
                        } else if ( (adr.equals(pData.getGaMAC())) || (adr.equals(pData.getGwMAC())) ){
                            gRemoteDevice[gCounter] = remoteDevice;
                            gCounter++;
                            System.out.println(adr);
                        } 
                    }
                }
                if (rCounter == 2){
                    redWocketsButton.setVisible(true);                    
                    jLabel2.setVisible(false);
                }
                if (gCounter == 2){
                    greenWocketsButton.setVisible(true);
                    jLabel2.setVisible(false);
                }
                if ((rCounter != 2) && (gCounter != 2)) {
                    jLabel2.setText("Your default sensors are not been detected. Please make sure");
                    jLabel4.setText("your default sensors have enough charge and are separaed from charger.");
                }
            } catch (IOException ex) {
                Logger.getLogger(ConnectPanel.class.getName()).log(Level.SEVERE, null, ex);
            }
        }            
    };
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JButton greenWocketsButton;
    private javax.swing.JLabel jLabel1;
    private javax.swing.JLabel jLabel2;
    private javax.swing.JLabel jLabel3;
    private javax.swing.JLabel jLabel4;
    private javax.swing.JButton redWocketsButton;
    // End of variables declaration//GEN-END:variables
}
