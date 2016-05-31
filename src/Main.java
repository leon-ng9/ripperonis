import java.awt.*;
import java.awt.event.*;
import javax.*;
import javax.swing.*;

public class Main {

	public static void main(String[] args) {
		// TODO Auto-generated method stub
		SwingUtilities.invokeLater(new Runnable() {
			
			@Override
			public void run() {
				MainWindow game = new MainWindow();
				game.setVisible(true);
			}
		});
	}

}
