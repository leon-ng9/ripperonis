import java.util.ArrayList;
import java.util.Random;

import javax.swing.SwingUtilities;

public class Main {

	public static void main(String[] args) {
		// TODO Auto-generated method stub
		SwingUtilities.invokeLater(new Runnable() {

			@Override
			public void run() {
				Random r = new Random();
				for(int j = 0; j < 100; j ++){
					String gender;
					if(r.nextBoolean()){
						gender = "M";
					}else{
						gender = "F";
					}
					int i = r.nextInt(100);
					String blood_type;
					if(i < 37){
						blood_type = "0+";
					}else if(i < 44) {
						blood_type = "0-";
					}else if(i < 80) {
						blood_type = "A+";
					}else if (i < 86){
						blood_type = "A-";
					}else if (i < 95){
						blood_type = "B+";
					}else if(i < 96) {
						blood_type = "B-";
					}else if(i < 99) {
						blood_type = "AB+";
					}else{
						blood_type = "AB-";
					}
					Util.donors.add(new Donor(String.valueOf(r.nextInt()),"seng2011", gender, blood_type, 1915 + r.nextInt(100), "040000000000"));
				}
				for(int i = 0; i < 1000; i ++){
					int index = Util.donors.size();
					Record rec =new Record(Util.donors.get(r.nextInt(index)),Util.map.getRandCity().getName());
					rec.blood = new Blood(r.nextInt(900) + 100, rec.donor, Util.batmobile);
					rec.blood.hospital = Util.hospital;
					rec.state = r.nextInt(4);
					Util.records.add(rec);
				}
				
				MainWindow game = new MainWindow();
				game.setVisible(true);


			};
		});};

}
