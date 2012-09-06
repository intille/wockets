package UserInterface;

import bluetooth.PcClient;
import java.awt.CardLayout;
import java.io.IOException;
import java.util.Vector;
import java.util.logging.Level;
import java.util.logging.Logger;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.SwingUtilities;

/**
 *
 * @author Aida
 */
public class StartPanel extends javax.swing.JPanel {

    JPanel userProcessContainer;
    
    public StartPanel(JPanel upc) {
        initComponents();
        userProcessContainer = upc;
        //textField.setVisible(false);
    }

    
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        jLabel1 = new javax.swing.JLabel();
        jLabel3 = new javax.swing.JLabel();
        showWocketsjButton = new javax.swing.JButton();
        messageLabel = new javax.swing.JLabel();

        jLabel1.setFont(new java.awt.Font("Tahoma", 0, 18)); // NOI18N
        jLabel1.setText("PC-Wocket Application");

        jLabel3.setFont(new java.awt.Font("Tahoma", 0, 14)); // NOI18N
        jLabel3.setText("Finding Wockets");

        showWocketsjButton.setText("Show Available Wockets");
        showWocketsjButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                showWocketsjButtonActionPerformed(evt);
            }
        });

        messageLabel.setFont(new java.awt.Font("Tahoma", 1, 12)); // NOI18N
        messageLabel.setText("                              ");

        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(this);
        this.setLayout(layout);
        layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addGroup(layout.createSequentialGroup()
                        .addGap(109, 109, 109)
                        .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                            .addComponent(jLabel1)
                            .addGroup(layout.createSequentialGroup()
                                .addGap(39, 39, 39)
                                .addComponent(jLabel3))))
                    .addGroup(layout.createSequentialGroup()
                        .addGap(118, 118, 118)
                        .addComponent(showWocketsjButton))
                    .addGroup(layout.createSequentialGroup()
                        .addGap(62, 62, 62)
                        .addComponent(messageLabel, javax.swing.GroupLayout.DEFAULT_SIZE, 277, Short.MAX_VALUE)))
                .addGap(61, 61, 61))
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addContainerGap()
                .addComponent(jLabel1)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.UNRELATED)
                .addComponent(jLabel3)
                .addGap(40, 40, 40)
                .addComponent(showWocketsjButton)
                .addGap(85, 85, 85)
                .addComponent(messageLabel)
                .addContainerGap(76, Short.MAX_VALUE))
        );
    }// </editor-fold>//GEN-END:initComponents

    private void showWocketsjButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_showWocketsjButtonActionPerformed
        showWocketsjButton.setVisible(false);
        messageLabel.setText("Searching for Wockets...It may take a while...");        
        SwingUtilities.invokeLater(findRunnable); 
    }//GEN-LAST:event_showWocketsjButtonActionPerformed

    Runnable findRunnable = new Runnable() {
        public void run() { 
            try {
                PcClient.findDevices();                    
                Vector btDevices = PcClient.vecDevices;
                JPanel connectPanel =  new ConnectPanel(userProcessContainer, btDevices);
                userProcessContainer.add("ConnectPanel",connectPanel);
                CardLayout c1 = (CardLayout)userProcessContainer.getLayout();
                c1.next(userProcessContainer);
            } catch (IOException ex) {
                Logger.getLogger(ConnectPanel.class.getName()).log(Level.SEVERE, null, ex);
            }
        }            
    };
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JLabel jLabel1;
    private javax.swing.JLabel jLabel3;
    private javax.swing.JLabel messageLabel;
    private javax.swing.JButton showWocketsjButton;
    // End of variables declaration//GEN-END:variables
}
