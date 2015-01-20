package Client;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.net.ServerSocket;
import java.net.Socket;

public class ServerSimulator extends Thread {

	private Socket acceptedSocket;
	
	public ServerSimulator()	{
		int port = 2220;
		ServerSocket socket;
		try {
			socket = new ServerSocket(port);
			acceptedSocket = socket.accept();
			System.out.println("Server found client");
			BufferedReader reader = new BufferedReader(new InputStreamReader(acceptedSocket.getInputStream()));
			while(true)	{
				System.out.println("Yes");
				System.out.println(reader.readLine());
				
			}
		} catch(Exception e)	{
			
		}
	}
	
	public void run()	{
		try {
			while(true)	{
				PrintWriter writer = new PrintWriter(acceptedSocket.getOutputStream(), true);
				writer.println(System.in);
			}
		} catch (IOException e) {

		}
	}
	 
	
	public static void main(String[] args)	{
		Thread a = new ServerSimulator();
		a.start();
	}
}