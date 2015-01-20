package Client;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.net.ServerSocket;
import java.net.Socket;

public class ServerSimulator {

	public ServerSimulator()	{
		int port = 8080;
		ServerSocket socket;
		try {
			socket = new ServerSocket(port);
			Socket acceptedSocket = socket.accept();
			System.out.println("Server found client");
			BufferedReader reader = new BufferedReader(new InputStreamReader(acceptedSocket.getInputStream()));
			while(true)	{
				System.out.println(reader.readLine());
			}
		} catch(Exception e)	{
			
		}
	}
	
	public static void main(String[] args)	{
		new ServerSimulator();
	}
}
