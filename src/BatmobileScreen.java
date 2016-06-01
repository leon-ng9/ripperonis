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
	private Record curr;

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
		
		JLabel title = new JLabel("<HTML><font size='10'>Requests to Donate</font><br><br></HTML>");
		title.setForeground(Color.WHITE);
		leftScreen.add(title, gbc);

		Hashtable<Record, String> closestRequests = this.bm.closestRequest();
		for (Record r : closestRequests.keySet()) {
			gbc.gridy += 1;
			
			JPanel request = new JPanel(new GridBagLayout());
			request.setOpaque(false);

			leftScreen.add(request, gbc);
			
			GridBagConstraints requestGBC = new GridBagConstraints();
			
			requestGBC.gridx = 0;
			requestGBC.gridy = 1;
			JLabel recordDetails = new JLabel(r.getDetails());
			recordDetails.setForeground(Color.WHITE);
			request.add(recordDetails, requestGBC);

			requestGBC.gridy = 2;
			JLabel string = new JLabel("Path: " + closestRequests.get(r));
			string.setForeground(Color.WHITE);
			request.add(string, requestGBC);
			
			requestGBC.gridy = 3;
			requestGBC.gridx = 0;
			
			JButton accept = new JButton("Accept");
			accept.addActionListener(new AddListener(r, mw, bm));
			request.add(accept, requestGBC);
			
			requestGBC.gridx = 1;
			JButton reject = new JButton("Reject");
			reject.addActionListener(new RejectListener(r,mw,bm));
			request.add(reject, requestGBC);
			
			requestGBC.gridy = 4;
			request.add(new JLabel(" "), requestGBC);
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
			curr = r;
			JPanel confirmationPanel = new JPanel();
			confirmationPanel.setOpaque(false);
			JButton accept = new JButton("Accept");
			accept.addActionListener(new AddListener(r, mw, bm));
			confirmationPanel.add(accept);
			JButton reject = new JButton("Reject");
			reject.addActionListener(new RejectListener(r,mw,bm));
			confirmationPanel.add(reject);
			pendingPanel.add(confirmationPanel);

			gbc.gridy += 1;
		}
	}

  private class AddListener implements ActionListener{
    private Record r;
    private MainWindow mw;
    private Batmobile bm;
    public AddListener(Record r, MainWindow mw, Batmobile bm){
      this.r = r;
        this.bm = bm;
        this.mw = mw;
    }

    public void actionPerformed(ActionEvent e){
      r.state = 1;
      mw.switchToBatmobile(bm);
    }

  }

  private class RejectListener implements ActionListener{
    private Record r;
    private MainWindow mw;
    private Batmobile bm;
    public RejectListener(Record r, MainWindow mw, Batmobile bm){
      this.r = r;
        this.bm = bm;
        this.mw = mw;
        bm.cityName = r.cityname;
    }

    public void actionPerformed(ActionEvent e){
      r.state = -1;
      mw.switchToBatmobile(bm);
    }

  }

}
