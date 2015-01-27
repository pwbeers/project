package modelTest;

import static org.junit.Assert.*;
import org.junit.Test;
import Model.Field;

public class FieldTest {
	
	@Test
	public void test() {
		isEmptyTest();
		isFieldTest();
	}
	
	public void isEmptyTest()	{
		Field field = new Field();
		assertEquals(true, field.isEmpty());
		field.setField(1);
		assertEquals(false, field.isEmpty());
		field.setField(2);
		assertEquals(false, field.isEmpty());
		field.setField(0);
		assertEquals(true, field.isEmpty());
	}
	
	public void isFieldTest()	{
		Field field = new Field();
		assertEquals(false, field.isField(1));
		assertEquals(false, field.isField(2));
		field.setField(1);
		assertEquals(true, field.isField(1));
		assertEquals(false, field.isField(2));
		field.setField(2);
		assertEquals(false, field.isField(1));
		assertEquals(true, field.isField(2));
		field.setField(0);
		assertEquals(false, field.isField(1));
		assertEquals(false, field.isField(2));
	}
}
