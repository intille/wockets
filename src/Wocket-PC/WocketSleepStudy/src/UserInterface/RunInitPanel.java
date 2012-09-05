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
import wockets.data.ParticipantData;

/**
 *
 * @author Aida
 */
public class RunInitPanel extends javax.swing.JPanel {

    JPanel userProcessContainer;
    ParticipantData pData = new ParticipantData();
    
    
    public RunInitPanel(JPanel upc, ParticipantData pd) {
        initComponents();
        userProcessContainer = upc;
        pData = pd;
    }

    
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        jLabel1 = new javax.swing.JLabel();
        jLabel3 = new javax.swing.JLabel();
        initializeButton = new javax.swing.JButton();
        runButton = new javax.swing.JButton();
        setWocketsjButton = new javax.swing.JButton();

        jLabel1.setFont(new java.awt.Font("Tahoma", 0, 18)); // NOI18N
        jLabel1.setText("PC-Wocket Application");

        jLabel3.setFont(new java.awt.Font("Tahoma", 0, 14)); // NOI18N
        jLabel3.setText("Finding Wockets");

        initializeButton.setText("Initialize new participant");
        initializeButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                initializeButtonActionPerformed(evt);
            }
        });

        runButton.setText("Start data Collection");
        runButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                runButtonActionPerformed(evt);
            }
        });

        setWocketsjButton.setText("Set new Wockets");
        setWocketsjButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                setWocketsjButtonActionPerformed(evt);
            }
        });

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
                                .addGap(9, 9, 9)
                                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                                    .addComponent(initializeButton)
                                    .addGroup(layout.createSequentialGroup()
                                        .addGap(30, 30, 30)
                                        .addComponent(jLabel3))))))
                    .addGroup(layout.createSequentialGroup()
                        .addGap(126, 126, 126)
                        .addComponent(runButton))
                    .addGroup(layout.createSequentialGroup()
                        .addGap(135, 135, 135)
                        .addComponent(setWocketsjButton)))
                .addContainerGap(97, Short.MAX_VALUE))
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addContainerGap()
                .addComponent(jLabel1)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.UNRELATED)
                .addComponent(jLabel3)
                .addGap(78, 78, 78)
                .addComponent(runButton)
                .addGap(26, 26, 26)
                .addComponent(initializeButton)
                .addGap(27, 27, 27)
                .addComponent(setWocketsjButton)
                .addContainerGap(78, Short.MAX_VALUE))
        );
    }// </editor-fold>//GEN-END:initComponents

    private void initializeButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_initializeButtonActionPerformed
        JPanel initializationPanel =  new InitializationPanel(userProcessContainer, pData);
        userProcessContainer.add("initializationPanel",initializationPanel);        
        CardLayout c1 = (CardLayout)userProcessContainer.getLayout();
        c1.next(userProcessContainer);
    }//GEN-LAST:event_initializeButtonActionPerformed

    private void runButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_runButtonActionPerformed
        JPanel runPanel =  new RunPanel(userProcessContainer, pData);
        userProcessContainer.add("runPanel",runPanel);
        CardLayout c1 = (CardLayout)userProcessContainer.getLayout();
        c1.next(userProcessContainer);
    }//GEN-LAST:event_runButtonActionPerformed

    private void setWocketsjButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_setWocketsjButtonActionPerformed
        JPanel init2Panel =  new Init2Panel(userProcessContainer, pData);
        userProcessContainer.add("init2Panel",init2Panel);
        CardLayout c1 = (CardLayout)userProcessContainer.getLayout();
        c1.next(userProcessContainer);
    }//GEN-LAST:event_setWocketsjButtonActionPerformed

    
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JButton initializeButton;
    private javax.swing.JLabel jLabel1;
    private javax.swing.JLabel jLabel3;
    private javax.swing.JButton runButton;
    private javax.swing.JButton setWocketsjButton;
    // End of variables declaration//GEN-END:variables
}
