import java.awt.*;
import java.awt.event.*;
import java.util.Vector;

import javax.*;
import javax.swing.*;

@SuppressWarnings("serial")
public class LoginScreen extends JPanel {

	private MainWindow mainWindow;
	private String targetScreen;

	/**
	 * Creates a OptionsScreen containing a resolution picker, controls remapper, difficulty picker and return button.
	 * @param mainWindow The JFrame containing the OptionsScreen
	 */
	public LoginScreen (MainWindow mainWindow) {
		this.mainWindow = mainWindow;

		this.setLayout(new GridBagLayout());
		// hospital, donor, batmobile
		initTitle();
		initLoginPanel();
		initConfirmation();
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

	private void initTitle() {
		GridBagConstraints gbc = new GridBagConstraints();
		gbc.gridy = 0;
		
		JLabel title = new JLabel("Blood Management System");
		title.setForeground(Color.ORANGE);
		title.setFont(new Font("Devanagari MT", Font.PLAIN, 50));
		add(title, gbc);
	}
	
	/**
	 * Initializes a resolution drop-down menu. The menu contains standard resolutions
	 * supported by the user's native screen resolution.
	 */
	private void initLoginPanel() {

		GridBagConstraints gbc = new GridBagConstraints();
		gbc.gridy = 1;

		JPanel login = new JPanel(new GridLayout(2, 0));
		add(login, gbc);

		JPanel username = new JPanel();
		username.add(new JLabel("Username: "));
		username.add(new JTextField("", 10));
		login.add(username);

		JPanel password = new JPanel();
		password.add(new JLabel("Password: "));
		password.add(new JPasswordField("", 10));
		login.add(password);

		gbc.gridy = 2;
		add(new JLabel(" "), gbc);

		gbc.gridy = 3;
		JPanel type = new JPanel(new GridLayout(0, 2));
		add(type, gbc);

		type.add(new JLabel("User type: "));

		Vector<String> userType = new Vector<String>();

		userType.add("Donor");
		userType.add("Hospital");
		userType.add("Batmobile");

		// set default
		this.targetScreen = "Donor";

		JComboBox<String> userTypeCB = new JComboBox<String>(userType);
		userTypeCB.setSelectedIndex(0);
		userTypeCB.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				@SuppressWarnings("unchecked")
				JComboBox<String> cb = (JComboBox<String>)e.getSource();
				String userType = (String)cb.getSelectedItem();
				LoginScreen.this.targetScreen = userType;
			}
		});

		type.add(userTypeCB, gbc);
	}

	private void initConfirmation() {
		GridBagConstraints gbc = new GridBagConstraints();

		gbc.gridy = 4;
		add(new JLabel(" "), gbc);

		gbc.gridy = 5;

		JButton confirm = new JButton("Login");
		confirm.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) {
				if (targetScreen == "Donor") {
					LoginScreen.this.mainWindow.switchToDonor(Util.donors.get(0));
				} else if (targetScreen == "Hospital") {
					LoginScreen.this.mainWindow.switchToHospital(Util.hospital);
				} else if (targetScreen == "Batmobile") {
					LoginScreen.this.mainWindow.switchToBatmobile(Util.batmobile);
				}
			}
		});
		add(confirm, gbc);

		gbc.gridy = 6;
		add(new JLabel(" "), gbc);

		gbc.gridy = 7;
		JButton exit = new JButton("Exit");
		exit.addActionListener(new ActionListener() {
			@Override
			public void actionPerformed(ActionEvent e) {
				System.exit(0);
			}

		});
		add(exit, gbc);
	}
}
