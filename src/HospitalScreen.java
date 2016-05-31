import java.awt.*;
import java.awt.event.*;
import java.util.ArrayList;
import java.util.List;

import javax.*;
import javax.swing.*;

@SuppressWarnings("serial")
public class HospitalScreen extends JPanel {

	private MainWindow mainWindow;
	private Hospital hospital;
	
	public HospitalScreen (MainWindow mainWindow, Hospital hospital) {
		// Left half: display a list of all blood -- make sure i have access to these stuffs - .allAvailableBlood()
		// Right half: display a list of all pending requests -- .requests (pending requests? yup) -- a button remove(remove(request)) a button add(update(request))
		// Top: request blood (text field-- amount) request(int amount)
		// Bottom: summary of all blood level (bar chart? preferable)

		this.mainWindow = mainWindow;
		this.hospital = hospital;

		this.setLayout(new GridLayout(2, 2)); // 2 columns, 2 rows

		initUpperLeftScreen();
		initUpperRightScreen();
		initLowerLeftScreen();
		initLowerRightScreen();
	}

	
	@Override
	protected void paintComponent(Graphics g) {
		super.paintComponent(g);
		Image background = (new ImageIcon("resources/bg.jpg")).getImage();
		g.drawImage(background, 0, 0, getWidth(), getHeight(), null);
	}

	private void initUpperLeftScreen() {
		JPanel upperLeftScreen = new JPanel(new GridBagLayout());
		upperLeftScreen.setOpaque(false);
		add(upperLeftScreen);
		
		GridBagConstraints gbc = new GridBagConstraints();
		gbc.gridy = 0;
		
		ArrayList<Blood> availableBloods = hospital.getAvailableBlood();
		for (Blood b : availableBloods) {
			JLabel bloodDetails = new JLabel(b.printDetails());
			bloodDetails.setForeground(Color.WHITE);
			upperLeftScreen.add(bloodDetails, gbc);
			gbc.gridy += 1;
		}
	}
	
	private void initUpperRightScreen() {
		JPanel upperRightScreen = new JPanel(new GridBagLayout());
		upperRightScreen.setOpaque(false);
		add(upperRightScreen);
		
		GridBagConstraints gbc = new GridBagConstraints();
		gbc.gridy = 0;
		
		List<Record> pendingRecords = hospital.getPendingRecords();
		for (Record r : pendingRecords) {
			JPanel pendingPanel = new JPanel(new GridLayout(2, 0));
			upperRightScreen.add(pendingPanel, gbc);
			
			JLabel bloodDetails = new JLabel(r.getDetails());
			bloodDetails.setForeground(Color.WHITE);
			pendingPanel.add(bloodDetails);
			
			JPanel confirmationPanel = new JPanel();
			JButton accept = new JButton("Accept");
			confirmationPanel.add(accept);
			JButton reject = new JButton("Reject");
			confirmationPanel.add(reject);
			
			gbc.gridy += 1;
		}
		
		
	}
	
	private void initLowerLeftScreen() {
		JPanel lowerLeftScreen = new JPanel(new GridBagLayout());
		lowerLeftScreen.setOpaque(false);
		add(lowerLeftScreen);
		
		GridBagConstraints gbc = new GridBagConstraints();
	}

	private void initLowerRightScreen() {
		JPanel lowerRightScreen = new JPanel(new GridBagLayout());
		lowerRightScreen.setOpaque(false);
		add(lowerRightScreen);
		
		GridBagConstraints gbc = new GridBagConstraints();
	}
}

