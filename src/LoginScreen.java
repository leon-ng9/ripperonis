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

	/**
	 * Initializes a resolution drop-down menu. The menu contains standard resolutions
	 * supported by the user's native screen resolution.
	 */
	private void initLoginPanel() {

		GridBagConstraints gbc = new GridBagConstraints();
		gbc.gridy = 0;
		
		JPanel username = new JPanel();
		username.add(new JLabel("Username: "));
		username.add(new JTextField("", 10));
		add(username, gbc);

		gbc.gridy = 1;
		JPanel password = new JPanel();
		password.add(new JLabel("Password: "));
		password.add(new JPasswordField("", 10));
		add(password, gbc);

		gbc.gridy = 2;
		// user type
		Vector<String> userType = new Vector<String>();

		userType.add("Donor");
		userType.add("Hospital");
		userType.add("Bat-mobile");

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

		add(userTypeCB, gbc);
	}

	private void initConfirmation() {
		GridBagConstraints gbc = new GridBagConstraints();
		gbc.gridy = 3;
		
		JButton confirm = new JButton("Login");
		confirm.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) {
				if (targetScreen == "Donor") {
					LoginScreen.this.mainWindow.switchToDonor(new Donor("Leon", "password", "Male", "AB-", 1996, "0400000000"));
				} else if (targetScreen == "Hospital") {
					LoginScreen.this.mainWindow.switchToHospital();
				} else if (targetScreen == "Batmobile") {
					LoginScreen.this.mainWindow.switchToBatmobile();
				}
			}
		});
		add(confirm, gbc);
	}
}

