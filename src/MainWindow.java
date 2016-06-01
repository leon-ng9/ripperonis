import java.awt.*;
import java.awt.event.*;
import javax.*;
import javax.swing.*;


@SuppressWarnings("serial")
public class MainWindow extends JFrame {

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
		System.out.println(Util.batmobile.closestRequest());
    // System.out.println(Util.donors);
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

	public void switchToHospital(Hospital hospital) {
		screens.add(new HospitalScreen(this, hospital), "Hospital");
		CardLayout cl = (CardLayout) screens.getLayout();
		cl.show(screens, "Hospital");
	}

	public void switchToBatmobile(Batmobile bm) {
		screens.add(new BatmobileScreen(this, bm), "Batmobile");
		CardLayout cl = (CardLayout) screens.getLayout();
		cl.show(screens, "Batmobile");
	}

	private JPanel screens; // contains all the screens of the game
}
