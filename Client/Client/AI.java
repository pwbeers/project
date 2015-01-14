package Client;

import Model.Model;
import Server.*;

public interface AI {

	/**
	 * 
	 * @param modelCopy
	 * @param controller
	 */
	void AI(Model modelCopy, ClientController controller);

	String doMove();

	String getHint();

}