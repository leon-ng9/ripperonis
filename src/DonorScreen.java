import java.awt.*;
import java.awt.event.*;
import java.util.Collections;

import javax.*;
import javax.swing.*;

@SuppressWarnings("serial")
public class DonorScreen extends JPanel {
	private MainWindow mw;
	private Donor donor;
	private JPanel bottomScreen;

	public DonorScreen(MainWindow mw, Donor donor) {
		this.mw = mw;
		this.donor = donor;
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
				DonorScreen.this.mw.switchToLogin();
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
		gbcScreen.weightx = 1;
		gbcScreen.weighty = 0.9;
		gbcScreen.fill = GridBagConstraints.BOTH;

		JPanel leftScreen = new JPanel(new GridBagLayout());
		leftScreen.setOpaque(false);
		bottomScreen.add(leftScreen, gbcScreen);

		GridBagConstraints gbc = new GridBagConstraints();
		gbc.gridy = 0;
		for (Record r : this.donor.records) {
			JPanel recordPanel = new JPanel();
			leftScreen.add(recordPanel, gbc);
			gbc.gridy += 1;

			JLabel stateLabel = new JLabel("State: " + r.state);
			recordPanel.add(stateLabel);

			// blood stuff (to do)
			if(r.blood != null){
				JLabel bloodLabel = new JLabel(r.blood.printDetails());
				recordPanel.add(bloodLabel);
			}
		}


		JButton sort = new JButton("Sort");
		sort.addActionListener(new ActionListener(){

			@Override
			public void actionPerformed(ActionEvent e) {
				donor.sortRecordByUpdateDate();
				DonorScreen.this.mw.switchToDonor(DonorScreen.this.donor);

			}
		});
		leftScreen.add(sort, gbc);


		JButton group = new JButton("Group");
		group.addActionListener(new ActionListener(){

			@Override
			public void actionPerformed(ActionEvent e) {
				donor.groupByStatus();
				DonorScreen.this.mw.switchToDonor(DonorScreen.this.donor);
			}
		});
		leftScreen.add(group, gbc);




	}


	private void initRightScreen() {
		GridBagConstraints gbcScreen = new GridBagConstraints();
		gbcScreen.gridy = 1;
		gbcScreen.weightx = 1;
		gbcScreen.weighty = 0.9;
		gbcScreen.fill = GridBagConstraints.BOTH;

		JPanel rightScreen = new JPanel(new GridBagLayout());
		rightScreen.setOpaque(false);
		bottomScreen.add(rightScreen, gbcScreen);

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
		JPanel amountApp = new JPanel();
		amountApp.add(new JLabel("Enter amount: "));
		final JTextField bloodAmount = new JTextField("", 10);
		amountApp.add(cityName);
		rightScreen.add(amountApp, gbc);

		gbc.gridy = 3;
		JButton update = new JButton("Update");
		update.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) {
				DonorScreen.this.donor.cityName = cityName.getText();
				Record record = new Record(donor, cityName.getText());
				record.blood = new Blood(Integer.parseInt(bloodAmount.getText()), donor, Util.batmobile);
				donor.addRecord(record);
				DonorScreen.this.mw.switchToDonor(DonorScreen.this.donor);
			}
		});
		rightScreen.add(update, gbc);

		gbc.gridy = 3;
		JLabel details = new JLabel(this.donor.getDetails());
		details.setForeground(Color.WHITE);
		rightScreen.add(details, gbc);
	}
}
