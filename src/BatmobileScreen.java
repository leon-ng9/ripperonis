import java.awt.*;
import java.awt.event.*;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Hashtable;
import java.util.List;

import javax.*;
import javax.swing.*;

@SuppressWarnings("serial")
public class BatmobileScreen extends JPanel {
	private MainWindow mw;
	private Batmobile bm;
	private JPanel bottomScreen;
	
	public BatmobileScreen(MainWindow mw, Batmobile bm) {
		this.mw = mw;
		this.bm = bm;
		this.setLayout(new GridBagLayout()); 

		initTopBar();
		
		bottomScreen = new JPanel(new GridBagLayout());
		bottomScreen.setOpaque(false);
		GridBagConstraints gbc = new GridBagConstraints();
		gbc.gridy = 1;
		gbc.weighty = 1;
		gbc.fill = GridBagConstraints.BOTH;
		add(bottomScreen, gbc);
		
		initLeftScreen();
		initRightScreen();
	}
	
	/**
	 * Paints a background image for the OptionsScreen
	 */
	@Override
	protected void paintComponent(Graphics g) {
		super.paintComponent(g);
		Image background = (new ImageIcon("resources/bg.jpg")).getImage();
		g.drawImage(background, 0, 0, getWidth(), getHeight(), null);
	}

	private void initTopBar() {
		JPanel topBar = new JPanel(new FlowLayout(FlowLayout.RIGHT));
		topBar.setOpaque(false);
		JButton logout = new JButton("Logout");
		logout.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent e) {
				BatmobileScreen.this.mw.switchToLogin();
			}
			
		});
		topBar.add(logout);
		
		GridBagConstraints gbc = new GridBagConstraints();
		gbc.weightx = 1;
		gbc.weighty = 0.1;
		gbc.gridy = 0;
		gbc.fill = GridBagConstraints.BOTH; // hack
		add(topBar, gbc);
	}
	
	private void initLeftScreen() {
		GridBagConstraints gbcScreen = new GridBagConstraints();
		gbcScreen.gridy = 1;
		gbcScreen.gridx = 0;
		gbcScreen.weightx = 1;
		gbcScreen.weighty = 0.9;
		gbcScreen.fill = GridBagConstraints.BOTH;
		
		JPanel leftScreen = new JPanel(new GridBagLayout());
		leftScreen.setOpaque(false);
		bottomScreen.add(leftScreen, gbcScreen);

		GridBagConstraints gbc = new GridBagConstraints();
		gbc.gridy = 0;
		
		Hashtable<Record, String> closestRequests = this.bm.closestRequest(); 
		for (Record r : closestRequests.keySet()) {
			JPanel request = new JPanel(new GridLayout(2, 0));
			request.setOpaque(false);
			leftScreen.add(request, gbc);
			
			JLabel recordDetails = new JLabel(r.getDetails());
			recordDetails.setForeground(Color.WHITE);
			leftScreen.add(recordDetails, gbc);
			
			JLabel string = new JLabel(closestRequests.get(r));
			string.setForeground(Color.WHITE);
			leftScreen.add(string, gbc);
			
			gbc.gridy += 1;
		}
		

		
	}


	private void initRightScreen() {
		GridBagConstraints gbcScreen = new GridBagConstraints();
		gbcScreen.gridy = 1;
		gbcScreen.gridx = 1;
		gbcScreen.weightx = 1;
		gbcScreen.weighty = 0.9;
		gbcScreen.fill = GridBagConstraints.BOTH;
		
		JPanel rightScreen = new JPanel(new GridBagLayout());
		rightScreen.setOpaque(false);
		JScrollPane scrollFrame = new JScrollPane(rightScreen);
		scrollFrame.getViewport().setOpaque(false);
		scrollFrame.setOpaque(false);
		bottomScreen.add(scrollFrame, gbcScreen);
		
		GridBagConstraints gbc = new GridBagConstraints();
		gbc.gridy = 0;
		
		List<Record> pendingRecords = bm.getPendingRecords();
		for (Record r : pendingRecords) {
			JPanel pendingPanel = new JPanel(new GridLayout(2, 0));
			pendingPanel.setOpaque(false);
			rightScreen.add(pendingPanel, gbc);
			
			JLabel bloodDetails = new JLabel(r.getDetails());
			bloodDetails.setForeground(Color.WHITE);
			pendingPanel.add(bloodDetails);
			
			JPanel confirmationPanel = new JPanel();
			confirmationPanel.setOpaque(false);
			JButton accept = new JButton("Accept");
			confirmationPanel.add(accept);
			JButton reject = new JButton("Reject");
			confirmationPanel.add(reject);
			pendingPanel.add(confirmationPanel);
			
			gbc.gridy += 1;
		}
	}
}