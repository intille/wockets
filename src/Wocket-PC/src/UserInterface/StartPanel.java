package UserInterface;

import java.awt.CardLayout;
import javax.swing.JOptionPane;
import javax.swing.JPanel;

/**
 *
 * @author Aida
 */
public class StartPanel extends javax.swing.JPanel {

    JPanel userProcessContainer;
    
    public StartPanel(JPanel upc) {
        initComponents();
        userProcessContainer = upc;
        messageTextField.setVisible(false);
    }

    
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        jLabel1 = new javax.swing.JLabel();
        jLabel3 = new javax.swing.JLabel();
        showWockets = new javax.swing.JButton();
        messageTextField = new javax.swing.JTextField();

        jLabel1.setFont(new java.awt.Font("Tahoma", 0, 18)); // NOI18N
        jLabel1.setText("PC-Wocket Application");

        jLabel3.setFont(new java.awt.Font("Tahoma", 0, 14)); // NOI18N
        jLabel3.setText("Finding Wockets");

        showWockets.setText("Show Available Wockets");
        showWockets.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                showWocketsActionPerformed(evt);
            }
        });

        messageTextField.setText("   ");

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
                        .addComponent(showWockets))
                    .addGroup(layout.createSequentialGroup()
                        .addGap(42, 42, 42)
                        .addComponent(messageTextField, javax.swing.GroupLayout.PREFERRED_SIZE, 303, javax.swing.GroupLayout.PREFERRED_SIZE)))
                .addContainerGap(55, Short.MAX_VALUE))
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addContainerGap()
                .addComponent(jLabel1)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.UNRELATED)
                .addComponent(jLabel3)
                .addGap(40, 40, 40)
                .addComponent(showWockets)
                .addGap(41, 41, 41)
                .addComponent(messageTextField, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addContainerGap(115, Short.MAX_VALUE))
        );
    }// </editor-fold>//GEN-END:initComponents

    private void showWocketsActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_showWocketsActionPerformed
        JOptionPane.showMessageDialog(null, "Searching for Wockets...It may take a while...");
        messageTextField.setVisible(true);
        messageTextField.setText("Searching for Wockets...It may take a while...");
        JPanel connectPanel =  new ConnectPanel(userProcessContainer);
        userProcessContainer.add("ConnectPanel",connectPanel);
        CardLayout c1 = (CardLayout)userProcessContainer.getLayout();
        c1.next(userProcessContainer);
        
    }//GEN-LAST:event_showWocketsActionPerformed

    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JLabel jLabel1;
    private javax.swing.JLabel jLabel3;
    private javax.swing.JTextField messageTextField;
    private javax.swing.JButton showWockets;
    // End of variables declaration//GEN-END:variables
}
