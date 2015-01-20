package Error;

/**
 * Handles the exceptions and errors from all classes in the server
 * @author Stephan *
 */
public class Error extends Exception{
	// ------------------ Instance variables ----------------
	private String errorMesssage; //A message to be displayed or send to a clien
	//------------------ Constructor ------------------------
	
	/**
	 * Sets up the variables
	 */
	public Error(String message){
		super(message);
	}
	
	// ------------------ Queries --------------------------
	// ------------------ Commands --------------------------
	/**
	 * Send an AMULET-ERROR message to the client, with an explanation in errorMessage
	 * @param errorMessage the message to be sent to the client
	 */
	public void clientError(String errorMessage){
		// TODO - implement Error.clientError
		throw new UnsupportedOperationException();
		
	}
	
	/**
	 * Prints an error message in the server GUI
	 * @param errorMessage the message to be displayed
	 */
	public void serverError(String errorMessage){
		// TODO - implement Error.serverError
		throw new UnsupportedOperationException();		
	}
	
	
}
