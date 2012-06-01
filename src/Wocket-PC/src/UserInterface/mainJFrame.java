package UserInterface;


import bluetooth.PcClient;
import java.awt.CardLayout;
import javax.swing.JPanel;

/**
 *
 * @author Aida Ehyaei
 */
public class mainJFrame extends javax.swing.JFrame {
    
    
    public mainJFrame() {
        initComponents();
        stopjButton.setVisible(false);
    }

    
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        jSplitPane1 = new javax.swing.JSplitPane();
        jPanel1 = new javax.swing.JPanel();
        startjButton = new javax.swing.JButton();
        stopjButton = new javax.swing.JButton();
        userProcessContainer = new javax.swing.JPanel();
        jScrollPane1 = new javax.swing.JScrollPane();
        jTextArea1 = new javax.swing.JTextArea();

        setDefaultCloseOperation(javax.swing.WindowConstants.EXIT_ON_CLOSE);
        setPreferredSize(new java.awt.Dimension(640, 480));

        jSplitPane1.setDividerLocation(120);

        startjButton.setText("Start");
        startjButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                startjButtonActionPerformed(evt);
            }
        });

        stopjButton.setText("Stop");
        stopjButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                stopjButtonActionPerformed(evt);
            }
        });

        org.jdesktop.layout.GroupLayout jPanel1Layout = new org.jdesktop.layout.GroupLayout(jPanel1);
        jPanel1.setLayout(jPanel1Layout);
        jPanel1Layout.setHorizontalGroup(
            jPanel1Layout.createParallelGroup(org.jdesktop.layout.GroupLayout.LEADING)
            .add(jPanel1Layout.createSequentialGroup()
                .addContainerGap()
                .add(jPanel1Layout.createParallelGroup(org.jdesktop.layout.GroupLayout.LEADING)
                    .add(startjButton, org.jdesktop.layout.GroupLayout.DEFAULT_SIZE, 99, Short.MAX_VALUE)
                    .add(stopjButton, org.jdesktop.layout.GroupLayout.DEFAULT_SIZE, 99, Short.MAX_VALUE))
                .addContainerGap())
        );
        jPanel1Layout.setVerticalGroup(
            jPanel1Layout.createParallelGroup(org.jdesktop.layout.GroupLayout.LEADING)
            .add(jPanel1Layout.createSequentialGroup()
                .add(155, 155, 155)
                .add(startjButton)
                .addPreferredGap(org.jdesktop.layout.LayoutStyle.RELATED)
                .add(stopjButton)
                .addContainerGap(152, Short.MAX_VALUE))
        );

        jSplitPane1.setLeftComponent(jPanel1);

        userProcessContainer.setLayout(new java.awt.CardLayout());

        jTextArea1.setColumns(20);
        jTextArea1.setFont(new java.awt.Font("Tahoma", 0, 13)); // NOI18N
        jTextArea1.setRows(5);
        jTextArea1.setText("\n\n\n\n\nWocket Calibration Program:\n\nThis program helps you to calibrate Wockets'\n  *Sampling rate\n  *Accelerometer\n  *Noise \n  *Battery\n\nYou need to have Wockets initialized and fully\ncharged before starting the calibration procedure.");
        jScrollPane1.setViewportView(jTextArea1);

        userProcessContainer.add(jScrollPane1, "card3");

        jSplitPane1.setRightComponent(userProcessContainer);

        getContentPane().add(jSplitPane1, java.awt.BorderLayout.CENTER);

        pack();
    }// </editor-fold>//GEN-END:initComponents

private void startjButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_startjButtonActionPerformed
    
    JPanel startPanel =  new StartPanel(userProcessContainer);
    userProcessContainer.add("StartPanel",startPanel);
    CardLayout c1 = (CardLayout)userProcessContainer.getLayout();
    c1.next(userProcessContainer);
    startjButton.setVisible(false);
    stopjButton.setVisible(true);
}//GEN-LAST:event_startjButtonActionPerformed

private void stopjButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_stopjButtonActionPerformed
    userProcessContainer.removeAll(); 
    PcClient.stop();
    stopjButton.setVisible(false);
    startjButton.setVisible(true);    
}//GEN-LAST:event_stopjButtonActionPerformed


    /**
     * @param args the command line arguments
     */
    public static void main(String args[]) {
        /* Set the Nimbus look and feel */
        //<editor-fold defaultstate="collapsed" desc=" Look and feel setting code (optional) ">
        /* If Nimbus (introduced in Java SE 6) is not available, stay with the default look and feel.
         * For details see http://download.oracle.com/javase/tutorial/uiswing/lookandfeel/plaf.html 
         */
        try {
            for (javax.swing.UIManager.LookAndFeelInfo info : javax.swing.UIManager.getInstalledLookAndFeels()) {
                if ("Nimbus".equals(info.getName())) {
                    javax.swing.UIManager.setLookAndFeel(info.getClassName());
                    break;
                }
            }
        } catch (ClassNotFoundException ex) {
            java.util.logging.Logger.getLogger(mainJFrame.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (InstantiationException ex) {
            java.util.logging.Logger.getLogger(mainJFrame.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (IllegalAccessException ex) {
            java.util.logging.Logger.getLogger(mainJFrame.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (javax.swing.UnsupportedLookAndFeelException ex) {
            java.util.logging.Logger.getLogger(mainJFrame.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        }
        //</editor-fold>

        /* Create and display the form */
        java.awt.EventQueue.invokeLater(new Runnable() {

            public void run() {
                new mainJFrame().setVisible(true);
                
            }
        });
    }
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JPanel jPanel1;
    private javax.swing.JScrollPane jScrollPane1;
    private javax.swing.JSplitPane jSplitPane1;
    private javax.swing.JTextArea jTextArea1;
    private javax.swing.JButton startjButton;
    private javax.swing.JButton stopjButton;
    private javax.swing.JPanel userProcessContainer;
    // End of variables declaration//GEN-END:variables
}
