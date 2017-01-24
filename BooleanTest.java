import java.util.*;

public class BooleanTest {
	
	public static void main(String[] args) {
		ArrayList<ArrayList<String>> test = new ArrayList<ArrayList<String>>();
		ArrayList<String> one = new ArrayList<String>();
		one.add("A");
		one.add("B");
		one.add("C");
		test.add(one);
		ArrayList<String> two = new ArrayList<String>();
		two.add("D");
		two.add("E");
		test.add(two);
		ArrayList<String> three = new ArrayList<String>();
		three.add("F");
		three.add("G");
		three.add("H");
		test.add(three);
		//System.out.println(distribute(test));
		System.out.println(reduce("ABDC","AB"));
	}

	public static ArrayList<String> distribute(ArrayList<ArrayList<String>> termsToMultiply) {
		ArrayList<ArrayList<String>> copy = new ArrayList<ArrayList<String>> (termsToMultiply);
		if(termsToMultiply.size() == 1) {return termsToMultiply.get(0);}
		ArrayList<String> ret = new ArrayList<String>();
		copy.remove(termsToMultiply.get(0));
		ArrayList<String> endings = distribute(copy);
		for (int i = 0; i < termsToMultiply.get(0).size(); i++) {
			for (int j = 0; j < endings.size(); j++) {
				ret.add(termsToMultiply.get(0).get(i) + endings.get(j));
			}
		}
		return ret;
	}

	public static String reduce(String t1, String t2) {
		// assume t1 has fewer characters than t2
		for(String c : t1.split("")) {
			if(t2.indexOf(c) == -1) {
				return "";
			}
		}
		return t1;
	}
}