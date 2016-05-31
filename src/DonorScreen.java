import java.awt.*;
import java.awt.event.*;
import java.util.Collections;

import javax.*;
import javax.swing.*;

@SuppressWarnings("serial")
public class DonorScreen extends JPanel {
	private MainWindow mw;
	private Donor donor;

	public DonorScreen(MainWindow mw, Donor donor) {
		this.mw = mw;
		this.donor = donor;
		this.setLayout(new GridLayout(0, 2)); // 2 columns 

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

	private void initLeftScreen() {
		JPanel leftScreen = new JPanel(new GridBagLayout());
		leftScreen.setOpaque(false);
		add(leftScreen);

		JButton sort = new JButton("Sort");
		sort.addActionListener(new ActionListener(){

			@Override
			public void actionPerformed(ActionEvent e) {
				donor.sortRecordByUpdateDate();
				DonorScreen.this.mw.switchToDonor(DonorScreen.this.donor);

			}
		});
		leftScreen.add(sort);


		JButton group = new JButton("Group");
		group.addActionListener(new ActionListener(){

			@Override
			public void actionPerformed(ActionEvent e) {
				donor.groupByStatus();
				DonorScreen.this.mw.switchToDonor(DonorScreen.this.donor);
			}
		});
		leftScreen.add(group);

		GridBagConstraints gbc = new GridBagConstraints();
		gbc.gridy = 0;

		for (Record r : this.donor.records) {
			JPanel recordPanel = new JPanel();
			leftScreen.add(recordPanel);
			gbc.gridy += 1;

			JLabel stateLabel = new JLabel("State: " + r.state);
			recordPanel.add(stateLabel);

			// blood stuff (to do)
			if(r.blood != null){
				JLabel bloodLabel = new JLabel("Blood: " + r.blood.toString());
				recordPanel.add(bloodLabel);
			}
		}
	}


	private void initRightScreen() {
		JPanel rightScreen = new JPanel(new GridBagLayout());
		rightScreen.setOpaque(false);
		add(rightScreen);

		GridBagConstraints gbc = new GridBagConstraints();

		// apply to donate
		gbc.gridy = 0;
		JLabel donate = new JLabel("Apply to donate");
		donate.setForeground(Color.WHITE);
		rightScreen.add(donate,gbc);
		
		gbc.gridy = 1;
		JPanel donationApplication = new JPanel();
		donationApplication.add(new JLabel("Enter city name: "));
		final JTextField cityName = new JTextField("", 10);
		donationApplication.add(cityName);
		rightScreen.add(donationApplication, gbc);
		
		gbc.gridy = 2;
		JButton update = new JButton("Update");
		update.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) {
				DonorScreen.this.donor.cityName = cityName.getText();
				Record record = new Record(donor, cityName.getText());
				donor.addRecord(record);
			}
		});
		rightScreen.add(update, gbc);
		
		gbc.gridy = 3;
		JLabel details = new JLabel(this.donor.getDetails());
		details.setForeground(Color.WHITE);
		rightScreen.add(details, gbc);

		
		
		
		
		
	}
}