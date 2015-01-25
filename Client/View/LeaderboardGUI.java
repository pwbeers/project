package View;

import javax.swing.JFrame;
import java.awt.FlowLayout;
import javax.swing.JTable;
import javax.swing.table.DefaultTableModel;

public class LeaderboardGUI extends Thread {

	private JFrame frame;
	private JTable table;
	private String[] leaderboard;

	/**
	 * Create the application.
	 */
	public LeaderboardGUI(String[] leaderboard) {
		this.leaderboard = leaderboard;
	}

	/**
	 * Initialize the contents of the frame.
	 */
	public void run() {
		frame = new JFrame();
		frame.setVisible(true);
		frame.setBounds(100, 100, 750, 500);
		frame.setDefaultCloseOperation(JFrame.HIDE_ON_CLOSE);
		frame.getContentPane().setLayout(new FlowLayout(FlowLayout.CENTER, 5, 5));
		table = new JTable();
		String[][] data = new String[leaderboard.length / 4][4];
		for (int i = 0; i < data.length; i++) {
			data[i][0] = leaderboard[i * 4];
			data[i][1] = leaderboard[i * 4 +1];
			data[i][2] = leaderboard[i * 4 +2];
			data[i][3] = leaderboard[i * 4 +3];
		}
		table.setModel(new DefaultTableModel(data,new String[] {"Player 1", "Player 2", "Time", "Result"}));
		table.getColumnModel().getColumn(0).setPreferredWidth(203);
		table.getColumnModel().getColumn(1).setPreferredWidth(208);
		table.getColumnModel().getColumn(2).setPreferredWidth(209);
		table.getColumnModel().getColumn(3).setPreferredWidth(136);
		frame.getContentPane().add(table);
		frame.validate();
	}
	
	/**
	 * Updates the data in this leaderboard GUI
	 * @param data
	 */
	public void updateData(String[] dataUpdate)	{
		frame.setVisible(true);
		leaderboard = dataUpdate;
		String[][] data = new String[leaderboard.length / 4][4];
		for (int i = 0; i < data.length; i++) {
			data[i][0] = leaderboard[i * 4];
			data[i][1] = leaderboard[i * 4 +1];
			data[i][2] = leaderboard[i * 4 +2];
			data[i][3] = leaderboard[i * 4 +3];
		}
		table.setModel(new DefaultTableModel(data,new String[] {"Player 1", "Player 2", "Time", "Result"}));
	}
}
