
package tester;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;

/**
 * Server. 
 * @author  Theo Ruys
 * @version 2005.02.21
 */
public class Server {
    private static final String USAGE = "usage: " + Server.class.getName() + " <name> <port>";

    /** Start een Server-applicatie op. */
    public static void main(String[] args) {
    	//Check argumenten
        if (args.length != 2) {
            System.out.println(USAGE);
            System.exit(0);
        }

        String name = args[0];
        int port = 0;
        ServerSocket server = null;

        // parse args[1] - the port
        try {
            port = Integer.parseInt(args[1]);
        } catch (NumberFormatException e) {
            System.out.println(USAGE);
            System.out.println("ERROR: port " + args[1] + " is not an integer");
            System.exit(0);
        }
        
    	//Start connection
    	try {
			server = new ServerSocket(port);
			Socket client = server.accept();
			Peer clientPeer = new Peer(name, client);
            Thread streamInputHandler = new Thread(clientPeer);
            streamInputHandler.start();
            clientPeer.handleTerminalInput();
            clientPeer.shutDown();
            server.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
    }

} // end of class Server
