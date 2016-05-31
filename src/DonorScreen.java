import java.awt.*;
import java.awt.event.*;
import java.util.Collections;

import javax.*;
import javax.swing.*;

public class DonorScreen extends JPanel {
	private MainWindow mw;
	private Donor donor;

	public DonorScreen(MainWindow mw, Donor donor) {
		this.mw = mw;
		this.donor = donor;
		this.setLayout(new GridLayout(2, 0)); // 2 columns 

		initLeftScreen();
		initRightScreen();
	}
	
	private void initLeftScreen() {
		JPanel leftScreen = new JPanel(new GridBagLayout());
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
		add(rightScreen);

		GridBagConstraints gbc = new GridBagConstraints();

		gbc.gridy = 1;
		rightScreen.add(new JLabel("Username: " + donor.username.toString()),gbc);
		gbc.gridy = 2;
		rightScreen.add(new JLabel("Gender: " + donor.gender.toString()),gbc);
		gbc.gridy = 3;
		rightScreen.add(new JLabel("Blood Type: " + donor.blood_type.toString()),gbc);
		gbc.gridy = 4;
		rightScreen.add(new JLabel("Year of Birth: " + donor.YOB),gbc);
		gbc.gridy = 5;
		rightScreen.add(new JLabel("Phone: " + donor.username.toString()),gbc);

		// apply to donate
		gbc.gridy = 6;
		rightScreen.add(new JLabel("Apply to donate"),gbc);
		gbc.gridy = 7;
		final JTextField cityName = new JTextField("Enter city name: ");
				rightScreen.add(cityName);
		gbc.gridy = 8;

		JButton update = new JButton("Update");

		update.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) {
				DonorScreen.this.donor.cityName = cityName.getText();
				Record record = new Record(donor, cityName.getText());
				donor.addRecord(record);
			}
		});
		rightScreen.add(update);
	}
}