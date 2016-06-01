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
		gbc.weightx = 1;
		gbc.weighty = 1;
		gbc.fill = GridBagConstraints.BOTH;


		gbc.gridy = 0;

		JPanel overallRecordPanel = new JPanel(new GridBagLayout());
		overallRecordPanel.setOpaque(false);
		JScrollPane scrollPane = new JScrollPane(overallRecordPanel);
		scrollPane.setOpaque(false);
		scrollPane.getViewport().setOpaque(false);
		leftScreen.add(scrollPane, gbc);

		gbc.gridy = 1;
		JLabel title = new JLabel("<HTML><font size='10'>Donation History</font><br><br></HTML>", SwingConstants.CENTER);
		title.setForeground(Color.WHITE);
		overallRecordPanel.add(title, gbc);


		for (Record r : this.donor.records) {
			gbc.gridy += 1;

			JPanel recordPanel = new JPanel(new GridBagLayout());
			recordPanel.setOpaque(false);
			overallRecordPanel.add(recordPanel, gbc);

			GridBagConstraints gbcRecord = new GridBagConstraints();
			gbcRecord.anchor = GridBagConstraints.LINE_START;
			gbcRecord.gridy = 0;

			JLabel stateLabel = new JLabel("", SwingConstants.LEFT);
			int state = r.state;
			if (state == 0) {
				stateLabel.setText("Status: Applying to donate");
			} else if (state == 1) {
				stateLabel.setText("Status: Being transported");
			} else if (state == 2) {
				stateLabel.setText("Status: Stored at a hospital");
			} else if (state == 3) {
				stateLabel.setText("Status: Used");
			}
			stateLabel.setForeground(Color.WHITE);

			recordPanel.add(stateLabel, gbcRecord);

			// blood stuff (to do)
			gbcRecord.gridy = 1;
			if(r.blood != null){
				JLabel bloodLabel = new JLabel(r.blood.printDetails());
				bloodLabel.setForeground(Color.WHITE);
				recordPanel.add(bloodLabel, gbcRecord);
			}

			gbcRecord.gridy = 2;
			recordPanel.add(new JLabel(" "), gbcRecord);
		}

		gbc.weighty = 0;
		JPanel buttons = new JPanel();
		buttons.setOpaque(false);
		leftScreen.add(buttons, gbc);

		JButton sort = new JButton("Sort");
		sort.addActionListener(new ActionListener(){

			@Override
			public void actionPerformed(ActionEvent e) {
				donor.sortRecordByUpdateDate();
				DonorScreen.this.mw.switchToDonor(DonorScreen.this.donor);

			}
		});
		buttons.add(sort, gbc);


		JButton group = new JButton("Group");
		group.addActionListener(new ActionListener(){

			@Override
			public void actionPerformed(ActionEvent e) {
				donor.groupByStatus();
				DonorScreen.this.mw.switchToDonor(DonorScreen.this.donor);
			}
		});
		buttons.add(group, gbc);




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
		JLabel donate = new JLabel("<HTML><font size='10'>Donation Application</font><br><br></HTML>");
		donate.setForeground(Color.WHITE);
		rightScreen.add(donate,gbc);

		gbc.gridy = 1;
		JLabel title = new JLabel("<HTML><u>Current Details</u></HTML>");
		title.setForeground(Color.WHITE);
		rightScreen.add(title, gbc);

		gbc.gridy = 2;
		JLabel details = new JLabel(this.donor.getDetails());
		details.setForeground(Color.WHITE);
		rightScreen.add(details, gbc);

		gbc.gridy = 3;
		rightScreen.add(new JLabel(" "), gbc);

		gbc.gridy = 4;
		JPanel donationApplication = new JPanel();
		donationApplication.add(new JLabel("Enter city name: "));
		final JTextField cityName = new JTextField("", 10);
		donationApplication.add(cityName);
		rightScreen.add(donationApplication, gbc);

		gbc.gridy = 6;
		JPanel amountApp = new JPanel();
		amountApp.add(new JLabel("Enter amount: "));
		final JTextField bloodAmount = new JTextField("", 10);
		amountApp.add(bloodAmount);
		rightScreen.add(amountApp, gbc);

		gbc.gridy = 8;
		JButton update = new JButton("Update");
		update.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) {
				DonorScreen.this.donor.cityName = cityName.getText();
				Record record = new Record(donor, cityName.getText());
				record.blood = new Blood(Integer.parseInt(bloodAmount.getText()), donor, Util.batmobile);
				DonorScreen.this.mw.switchToDonor(DonorScreen.this.donor);
			}
		});
		rightScreen.add(update, gbc);


	}
}
