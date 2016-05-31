import java.awt.*;
import java.awt.event.*;
import javax.*;
import javax.swing.*;


@SuppressWarnings("serial")
public class MainWindow extends JFrame {

	/**
	 * Creates a JFrame that contains all the components of the game including
	 * MenuScreen, GameScreen, TutorialScreen and OptionsScreen. 
	 * Initialized to display the MenuScreen first.
	 */
	public MainWindow() {
		// login, donor, batmobile, hospital
		screens = new JPanel(new CardLayout());
		add(screens);

		// configure the main window
		setSize(new Dimension(1600, 900));
		setLocationRelativeTo(null);
		setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

		// login screen
		LoginScreen login = new LoginScreen(this);
		screens.add(login, "Login");

		// hospital screen
		//HospitalScreen hospital = new HospitalScreen(this);
		//screens.add(hospital, "Hospital");

		// hospital screen
		//BatmobileScreen batmobile = new BatmobileScreen(this);
		//screens.add(batmobile, "Batmobile");

		// 
		switchToLogin(); // starting screen
	}

	public void switchToDonor(Donor donor) {
		// create a game with the options chosen in the OptionsScreen (or default if none chosen)
		screens.add(new DonorScreen(this, donor), "Donor");
		CardLayout cl = (CardLayout) screens.getLayout();
		cl.show(screens, "Donor");
	}

	public void switchToLogin() {
		CardLayout cl = (CardLayout) screens.getLayout();
		cl.show(screens, "Login");
	}

	public void switchToHospital() {
		CardLayout cl = (CardLayout) screens.getLayout();
		cl.show(screens, "Hospital");
	}

	public void switchToBatmobile() {
		CardLayout cl = (CardLayout) screens.getLayout();
		cl.show(screens, "Batmobile");
	}

	private JPanel screens; // contains all the screens of the game
}
