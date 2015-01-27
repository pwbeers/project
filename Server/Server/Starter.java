package Server;

import View.ServerGui;

public class Starter {
	public static void main(String[] args)	{
		ServerController controller = new ServerController();
		controller.writeToGUI("ServerController created");
	}


}
