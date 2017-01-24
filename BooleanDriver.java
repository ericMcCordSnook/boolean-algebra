// Eric McCord-Snook
// June 20, 2016

// 1. Prompts a user for a boolean expression, tests the expression for validity
// 2. Uses regular expression reduction of the expression to populate a truth table for the expression
// 3. Implements the Quine-McCluskey algorithm to find the reduced form of the boolean expression
//	  in product of sums form (also known as canonical form)

import java.util.*;

public class BooleanDriver {

	// initialize scanner for user input
	static Scanner keyboard = new Scanner(System.in);

	static int numVars;
	static int numBoolCombos;
	static ArrayList<String> vars;	// note: in alphabetical order when set
	static String boolExpr;
	static TreeMap<String, Boolean> truthTable;
	static ArrayList<String> minterms;
	static ArrayList<String> decimalMinterms;
	static ArrayList<String> primeImplicants = new ArrayList<String>();
	static ArrayList<String> essentialPrimeImplicants = new ArrayList<String>();
	static ArrayList<ArrayList<String>> additionalImplicants = new ArrayList<ArrayList<String>>();
	static ArrayList<String> implicantsToUse = new ArrayList<String>();
	static String reducedBoolExpr;

	public static void main(String[] args) {
		// indication of a successful build
		System.out.println("Boolean Driver running properly...");

		// number of variables in expression to aid input parsing
		numVars = getNumVarsFromUser();

		// valid expression as entered by user
		boolExpr = getBoolExprFromUser(numVars);

		// creating divider between input and results
		System.out.println("\n======================RESULTS======================");

		// number of spots in the K-map, expressions we need to try
		numBoolCombos = (int)Math.pow(2, numVars);
		
		// truth table hashmap initializer
		truthTable = new TreeMap<String, Boolean>();

		// call to populate the truth table with the correct values given the expression
		generateTruthTable();
		printTruthTable();

		// call to get the minterms from the truth table
		minterms = getMinterms();
		System.out.println("Binary Minterms: " + minterms);
		decimalMinterms = getDecimalMinterms();
		System.out.println("Decimal Minterms: " + decimalMinterms);

		// call to find prime implicants; recursive, so starts with the initial table of minterms
		setPrimeImplicants(getMintermsSortedByNumOnes());
		System.out.println("Prime Implicants: " + primeImplicants);

		// call to find essential prime implicants; uses the prime implicants, so no arguments
		setEssentialPrimeImplicants();
		System.out.println("Essential Prime Implicants: " + essentialPrimeImplicants);

		// remove essential prime implicants from primeImplicants 
		primeImplicants.removeAll(essentialPrimeImplicants);
		// use Petrick's method to find the rest of the implicants to use
		addNonEssentialImplicants();

		// print out all the possible solutions, must happen at least once
		int i = 0;
		do {

			implicantsToUse.clear();
			implicantsToUse.addAll(essentialPrimeImplicants);
			implicantsToUse.addAll(additionalImplicants.get(i));

			// call to get reduced boolean expression
			reducedBoolExpr = getReducedBoolExpr();
			System.out.println("Reduced boolean expression: " + reducedBoolExpr);

			i++;
		} while (i < additionalImplicants.size());
	}

	// returns the reduced boolean expression given the implicants needed to cover the whole expression
	public static String getReducedBoolExpr() {
		String ret = "";
		for (int i = 0; i < implicantsToUse.size() - 1; i++) {
			ret += getImplicantLiterals(implicantsToUse.get(i)) + " + ";
		}
		return ret + getImplicantLiterals(implicantsToUse.get(implicantsToUse.size() - 1));
	}

	// returns the letters needed to represent the given implicant
	public static String getImplicantLiterals(String imp) {
		String ret = "";
		String[] impArr = imp.split("");
		for (int i = 0; i < impArr.length; i++) {
			if (impArr[i].equals("-")) {continue;}
			ret += vars.get(i) + (impArr[i].equals("0") ? "'" : "");
		}
		return ret;
	}

	// adds the necessary nonessential implicants to the implicants to use arraylist using Petrick's method
	public static void addNonEssentialImplicants() {
		if (primeImplicants.size() == 0) { return; }
		// give each implicant a label 0-N
		String[] impLabels = new String[primeImplicants.size()];
		for (int i = 0; i < impLabels.length; i++) {
			impLabels[i] = "" + i;
		}

		// creates an arraylist of arraylists which represents the product of sums of implicants 
		ArrayList<ArrayList<String>> termsToMultiply = new ArrayList<ArrayList<String>>();
		for (int mt = 0; mt < minterms.size(); mt++) {
			ArrayList<String> termsToAdd = new ArrayList<String>();
			for (int imp = 0; imp < primeImplicants.size(); imp++) {
				if (implicantDoesCoverMinterm(primeImplicants.get(imp), minterms.get(mt))) {
					termsToAdd.add("" + imp);
				}
			}
			termsToMultiply.add(termsToAdd);
		}

		// distributes the product of sums into all the different combinations
		ArrayList<String> terms = distribute(termsToMultiply);

		// make each term in alphabetical order and remove duplicated letters
		for (int i = 0; i < terms.size(); i++) {
			ArrayList<String> uniqueAlphaLetters = getUniqueCharsInAlpha(terms.get(i));
			String cur = "";
			for (int j = 0; j < uniqueAlphaLetters.size(); j++) {
				cur += uniqueAlphaLetters.get(j);
			}
			terms.set(i, cur);
		}

		// remove duplicate terms from the terms ArrayList
		Set<String> removeDups = new LinkedHashSet<>(terms);
		terms = new ArrayList<String>(removeDups);

		// reduce the terms using X + XY = X 
		ArrayList<String> reducedTerms = reduceTerms(terms);

		// choose terms with fewest literals (shortest length)
		ArrayList<String> shortestTerms = getShortestTerms(reducedTerms);

		// compare number of literals in implicants from the shortest terms by:
		// 1. getting the full strings for the implicants used
		ArrayList<String> fullImplicantStrings = new ArrayList<String>();
		for (int term = 0; term < shortestTerms.size(); term++) {
			String tot = "";
			for (int imp = 0; imp < shortestTerms.get(term).length(); imp++) {
				tot += primeImplicants.get(Integer.parseInt(shortestTerms.get(term).substring(imp, imp+1)));
			}
			fullImplicantStrings.add(tot);
		}

		// 2. choosing those with the most dashes (-)
		ArrayList<Integer> nonessentialOptionsIndices = getNonessentialOptionsIndices(fullImplicantStrings);

		// add each minimal version to the arraylist of arraylists
		for (int i = 0; i < nonessentialOptionsIndices.size(); i++) {
			ArrayList<String> cur = new ArrayList<String>();
			String termString = shortestTerms.get(nonessentialOptionsIndices.get(i));
			for (String c : termString.split("")) {
				cur.add(primeImplicants.get(Integer.parseInt(c)));
			}
			additionalImplicants.add(cur);
		}
	}

	// returns an ArrayList of the indices of the full implicant strings with the most dashes (-)
	public static ArrayList<Integer> getNonessentialOptionsIndices(ArrayList<String> strs) {
		ArrayList<Integer> ret = new ArrayList<Integer>();
		int maxDashes = strs.get(0).length() - strs.get(0).replace("-", "").length();
		for(int i = 0; i < strs.size(); i++) {
			int curDashes = strs.get(i).length() - strs.get(i).replace("-","").length();
			if (curDashes == maxDashes) {
				ret.add(i);
			} else if (curDashes > maxDashes) {
				maxDashes = curDashes;
				ret.clear();
				ret.add(i);
			}
		}
		return ret;
	}

	// returns an ArrayList of the shortest term(s) from the list
	public static ArrayList<String> getShortestTerms(ArrayList<String> terms) {
		ArrayList<String> ret = new ArrayList<String>();
		int minLength = terms.get(0).length();
		for (int i = 0; i < terms.size(); i++) {
			String cur = terms.get(i);
			int curLen = cur.length();
			if (curLen == minLength) {
				ret.add(cur);
			} else if (curLen < minLength) {
				minLength = curLen;
				ret.clear();
				ret.add(cur);
			}
		}
		return ret;
	}

	// returns an ArrayList of the most reduced terms, performing replacements X + XY = X
	public static ArrayList<String> reduceTerms(ArrayList<String> terms) {
		Set<String> ret = new LinkedHashSet<String>();

		// iterate through each term
		for (int i = 0; i < terms.size(); i++) {
			boolean reducedFlag = false;
			// iterate through each of the following terms
			for (int j = i + 1; j < terms.size(); j++) {
				String str = compareAndReduceTwoStringTerms(terms.get(i), terms.get(j)); 
				if (!str.equals("")) {
					ret.add(str);
					reducedFlag = true;
				}
			}
			if (!reducedFlag) { ret.add(terms.get(i)); }
		}

		return new ArrayList<String>(ret);
	}

	// compares two strings and sees if one is a subset of the other,
	// if it is, then it returns the subset, otherwise it returns the empty string
	public static String compareAndReduceTwoStringTerms(String t1, String t2) {
		if(t1.length() == t2.length()) { 
			return ""; 			// no duplicates passed, so one can't be a subset of the other
		} else if (t1.length() < t2.length()) {
			// given t1 has fewer characters than t2
			for(String c : t1.split("")) {
				if(t2.indexOf(c) == -1) {
					return "";
				}
			}
			return t1;
		} else {
			// given t2 has fewer characters than t1
			for(String c : t2.split("")) {
				if(t1.indexOf(c) == -1) {
					return "";
				}
			}
			return t1;
		}
	}

	// distributes and lists terms in sum of products form
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

	// fills the string array of the essential prime implicants of the function
	// using the second part of the Quine-McCluskey Algorithm
	public static void setEssentialPrimeImplicants() {
		int numMinterms = minterms.size();
		// create and fill boolean array that tells which prime implicants cover which minterms
		boolean[][] primeImplicantTable = new boolean[primeImplicants.size()][numMinterms];
		for (int imp = 0; imp < primeImplicants.size(); imp++) {
			for (int mt = 0; mt < numMinterms; mt++) {
				primeImplicantTable[imp][mt] = implicantDoesCoverMinterm(primeImplicants.get(imp), minterms.get(mt));
			}
		}

		// count backwards to prevent indexing issues when removing items from minterms ArrayList
		for (int mt = numMinterms - 1; mt >= 0; mt--) {
			int impLocation = 0;
			int count = 0;
			for (int imp = 0; imp < primeImplicants.size(); imp++) {
				if (primeImplicantTable[imp][mt]) {
					impLocation = imp;
					count++;
				}
			}
			if (count == 1) {
				essentialPrimeImplicants.add(primeImplicants.get(impLocation));
				minterms.remove(mt);
			}
		}
		Set<String> removeDups = new LinkedHashSet<>(essentialPrimeImplicants);
		essentialPrimeImplicants = new ArrayList<String>(removeDups);
	}

	// returns true if the given prime implicant covers the given minterm
	public static boolean implicantDoesCoverMinterm(String imp, String mt) {
		for (int i = 0; i < mt.length(); i++) {
			String curImpChar = imp.substring(i, i+1);
			if (curImpChar.equals("-")) {continue;}
			if(!curImpChar.equals(mt.substring(i, i+1))) {return false;}
		}
		return true;
	}

	// fills the string array of the prime implicants of the function, 
	// using the first part of the Quine-McCluskey Algorithm
	// repeats as many times as necessary using recursion
	public static void setPrimeImplicants(ArrayList<ArrayList<String>> tableToCompare) {
		// initiate table of booleans to keep track of which terms have and have not been
		// added to the reduced table, so we can then add the unpaired terms to the prime implicants
		ArrayList<ArrayList<Boolean>> pairedArr = makeBoolTable(tableToCompare);

		// initiate reduced table to be sent by recursion to next step
		ArrayList<ArrayList<String>> reducedTable = new ArrayList<ArrayList<String>>();

		// iterate through each group of terms
		for (int level = 0; level < tableToCompare.size() - 1; level++) {
			// create ArrayList to be added to the reducedTable once pairs have been made
			ArrayList<String> reducedTermsPerLevel = new ArrayList<String>();
			// iterate through each term in the group
			for (int t1 = 0; t1 < tableToCompare.get(level).size(); t1++) {
				String term1 = tableToCompare.get(level).get(t1);
				// iterate through each term in the following group
				for (int t2 = 0; t2 < tableToCompare.get(level + 1).size(); t2++) {
					String term2 = tableToCompare.get(level + 1).get(t2);
					String reducedString = getReducedString(term1, term2);
					// add the reduced string to the reduced terms per level
					if (reducedString != null) {
						reducedTermsPerLevel.add(reducedString);
						pairedArr.get(level).set(t1, true);
						pairedArr.get(level + 1).set(t2, true);
					}
				}
			}

			// add all distinct reduced terms to the reduced table for a given level
			Set<String> removeDups = new LinkedHashSet<>(reducedTermsPerLevel);
			reducedTermsPerLevel = new ArrayList<String>(removeDups);
			reducedTable.add(reducedTermsPerLevel);
		}

		// add all the distinct unpaired terms to the prime implicants
		primeImplicants.addAll(uniqueUnpairedTerms(tableToCompare, pairedArr));

		// recur if there were any pairs made in the last step
		if (wereAnyPairs(pairedArr)) {
			setPrimeImplicants(reducedTable);
		}
	}

	// returns an arraylist of the unique unpaired terms
	public static ArrayList<String> uniqueUnpairedTerms(ArrayList<ArrayList<String>> strTable, ArrayList<ArrayList<Boolean>> pairedArr) {
		ArrayList<String> ret = new ArrayList<String>();
		for (int i = 0; i < strTable.size(); i++) {
			for (int j = 0; j < strTable.get(i).size(); j++) {
				if (!pairedArr.get(i).get(j)) { ret.add(strTable.get(i).get(j)); }
			}
		}
		Set<String> removeDups = new LinkedHashSet<>(ret);
		return new ArrayList<String>(removeDups);
	}

	// returns a boolean: true if anything was true, false if everything was false
	public static boolean wereAnyPairs(ArrayList<ArrayList<Boolean>> table) {
		for (int i = 0; i < table.size(); i++) {
			for (int j = 0; j < table.get(i).size(); j++) {
				if (table.get(i).get(j)) { return true; }
			}
		}
		return false;
	}

	// returns an arraylist of arraylists of booleans (all false) which will be used to flag if
	// a certain term has been paired up yet
	public static ArrayList<ArrayList<Boolean>> makeBoolTable(ArrayList<ArrayList<String>> table) {
		ArrayList<ArrayList<Boolean>> ret = new ArrayList<ArrayList<Boolean>>();
		for (int i = 0; i < table.size(); i++) {
			ArrayList<Boolean> subarr = new ArrayList<Boolean>();
			for (int j = 0; j < table.get(i).size(); j++) {
				subarr.add(false);
			}
			ret.add(subarr);
		}
		return ret;
	}

	// returns a string where a dash has replaced the single bit where the two argument strings differed
	// if they differed by more than one bit, it returns null
	public static String getReducedString(String str1, String str2) {
		int diffCount = 0;
		int indexToReplace = 0;
		for (int i = 0; i < str1.length(); i++) {
			if (!str1.substring(i, i + 1).equals(str2.substring(i, i + 1))) {
				diffCount++;
				indexToReplace = i;
			}
		}
		if (diffCount != 1) {return null;}
		return str1.substring(0, indexToReplace) + "-" + str1.substring(indexToReplace + 1, str1.length());
	}

	// returns a two dimensional string array where the first index of the array is the number of 1's
	// in each string and the second is which string in that set we are referring to
	public static ArrayList<ArrayList<String>> getMintermsSortedByNumOnes() {
		ArrayList<ArrayList<String>> ret = new ArrayList<ArrayList<String>>();
		for (int i = 0; i <= numVars; i++) {
			ArrayList<String> curMins = new ArrayList<String>();
			for (String min : minterms) {
				if (numOnes(min) == i) {
					curMins.add(min);
				}
			}
			ret.add(curMins);
		}
		return ret;
	}

	// returns the minterms from the truth table
	public static ArrayList<String> getMinterms() {
		ArrayList<String> mt = new ArrayList<String>();
		for (String s : truthTable.keySet()) {
			if(truthTable.get(s)) {
				mt.add(s);
			}
		}
		return mt;
	}

	// returns integer number of 1's in the bit string
	public static int numOnes(String str) {
		int ret = 0;
		String[] charArr = str.split("");
		for (String c : charArr) {
			if (c.equals("1")) { ret++; }
		}
		return ret;
	}

	// prints out the truth table
	public static void printTruthTable() {
		for(String key: truthTable.keySet()) {
			System.out.println("\""+ key +"\": " + truthTable.get(key));
		}
	}

	// populates the truth able wit the correct values given the booloean expression
	public static void generateTruthTable() {
		// first get the 2^numVars boolean strings to be used (e.g. ["00","01","10","11"])
		String[] keyStrings = new String[numBoolCombos];
		for (int i = 0; i < numBoolCombos; i++) {
			keyStrings[i] = getNBitStringForInt(i, numVars);
			truthTable.put(keyStrings[i], getTruthValueOfExpressionForBitString(keyStrings[i]));
		}
	}

	// determines if the boolean expression is true or false for the given bitstring
	public static boolean getTruthValueOfExpressionForBitString(String bits) {
		// create editable string for reduction
		String cur = boolExpr;

		// first replace variables with 1's and 0's
		for (int i = 0; i < bits.length(); i++) {
			cur = cur.replaceAll(vars.get(i), bits.substring(i, i+1));
		}

		// repeat until left with a single 0 or 1
		while(cur.length() != 1) {
			// next, replace all negated bits with the opposite
			while (cur.matches(".*[01]\\'.*")) {
				cur = cur.replaceAll("0\\'","1");
				cur = cur.replaceAll("1\\'","0");
			}
		
			// next, replace all bits directly next to each other with their product (0 unless 11 -> 1)
			while (cur.matches(".*[01][01].*")) {
				cur = cur.replaceAll("[01]?0[01]?","0");
				cur = cur.replaceAll("11", "1");
			}

			// next, replace all sums (or's) with simplest form
			while (cur.matches(".*(?<![\\)\\]])[01]\\+[01](?![\\(\\[]).*")) {
				cur = cur.replaceAll("(?<![\\)\\]])([01]\\+)?1(\\+[01])?(?![\\(\\[])","1");
				cur = cur.replaceAll("(?<![\\)\\]])0\\+0(?![\\(\\[])","0");
			}

			// next, eliminate parentheses around single bits
			while (cur.matches(".*\\([01]\\).*")) {
				cur = cur.replaceAll("\\(0\\)","0");
				cur = cur.replaceAll("\\(1\\)","1");
			}

			// last, eliminate square brackets around single bits
			while (cur.matches(".*\\[[01]\\].*")) {
				cur = cur.replaceAll("\\[0\\]","0");
				cur = cur.replaceAll("\\[1\\]","1");
			}
		}
		return cur.equals("1");
	}

	// recursively finds the n-bit binary string representing an integer
	public static String getNBitStringForInt(int i, int numChars) {
		if (numChars == 1) {
			return i + "";
		} else {
			int curPlace = (int)Math.pow(2, numChars - 1);
			int curInt = (i >= curPlace) ? 1 : 0;
			return curInt + getNBitStringForInt(i - curInt * curPlace, numChars - 1);	
		}
	}

	// finds the minterm represented by a binary string
	public static String getMintermFromBitString(String s) {
		int ret = 0;
		int power = s.length() - 1;
		String[] charArr = s.split("");
		for (String c : charArr) {
			if (c.equals("1")) {
				ret += Math.pow(2, power);
			}
			power--;
		}
		return ret + "";
	}

	// get minterm array in decimal from binary minterm array
	public static ArrayList<String> getDecimalMinterms() {
		ArrayList<String> ret = new ArrayList<String>();
		for (int i = 0; i < minterms.size(); i++) {
			ret.add(getMintermFromBitString(minterms.get(i)));
		}
		return ret;
	}

	// returns number of variables in expression, must be 2, 3, or 4
	// this is then required to be the number of vars in the input expression
	public static int getNumVarsFromUser() {
		System.out.println("\nEnter number of variables (2,3,4): ");
		String numVarsString = keyboard.nextLine().trim();
		
		switch (numVarsString) {
			case "2": return 2;
			case "3": return 3;
			case "4": return 4;
			default: return getNumVarsFromUser();
		}
	}

	// return string of a valid boolean expression that the user entered
	public static String getBoolExprFromUser(int numVars) {
		System.out.println("\nSample boolean expression: ab(c'+d) + (a'd + c)'");
		System.out.println("Enter boolean expression on the next line: ");

		// get string without whitespace and lowercase
		String rawText = keyboard.nextLine().trim().toLowerCase().replaceAll("\\s","");

		// test to be sure the user only entered legal characters
		if (!rawText.replaceAll("[a-z\\[\\]\\(\\)\\'\\+]","").isEmpty()) {
			System.out.println("You used an invalid character, only valid characters are letters a-z, [], (), +, and ', please try again.");
			return getBoolExprFromUser(numVars);
		}

		// test to be sure the user entered the correct number of variables
		String rawVarsOnly = rawText.replaceAll("[^a-z]","");
		boolean validNumVars = rawVarsOnly.chars().distinct().count() == numVars;
		if (!validNumVars) {
			System.out.println("Inconsistent number of variables, please try again.");
			return getBoolExprFromUser(numVars);
		}
		// here we set the variables in alphabetical order
		vars = getUniqueCharsInAlpha(rawVarsOnly);

		// test to be sure the grouping, negation, and disjunction operators used properly
		boolean properSpecialCharUse = properSpecialCharUse(rawText);
		if (!properSpecialCharUse) {
			System.out.println("You misused the grouping, negation, or disjunction operators, please try again.");
			return getBoolExprFromUser(numVars);
		}

		// TODO: more tests to ensure the boolean expession is valid

		return rawText;
	}

	// return true if and only if the special characters (non-letters) are used properly in this string
	public static boolean properSpecialCharUse(String rawText) {
		// test for even number of parentheses
		int numOpenPars = rawText.replaceAll("[^\\(]","").length();
		int numClosedPars = rawText.replaceAll("[^\\)]","").length();
		if (numOpenPars != numClosedPars) {
			System.out.println("Uneven open and closed parentheses.");
			return false;
		}

		// test for even number of square brackets
		int numOpenSqBrackets = rawText.replaceAll("[^\\[]","").length();
		int numClosedSqBrackets = rawText.replaceAll("[^\\[]","").length();
		if (numOpenSqBrackets != numClosedSqBrackets) {
			System.out.println("Uneven open and closed square brackets.");
			return false;
		}

		// test that + sign is only found between two letters, to the right of a close paren, or to the left of an open paren
		// can't be at the beginning or end of the expression either
		if (rawText.charAt(0) == '+' || rawText.charAt(rawText.length() - 1) == '+') {
			System.out.println("Cannot use '+' sign at beginning or end of expression.");
			return false;
		}

		// TODO: More tests to ensure the boolean expression is valid
		return true;
	}

	// return a string ArrayList containing the unique characters (variables) used in a boolean expression
	// return the array of letters in alphabetical order
	public static ArrayList<String> getUniqueCharsInAlpha(String rawVarsOnly) {
		String[] charArr = rawVarsOnly.split("");
		int end = charArr.length;
		Set<String> charSet = new HashSet<String>();
		for (int i = 0; i < end; i++) {
  			charSet.add(charArr[i]);
		}
		ArrayList<String> ret = new ArrayList<String>();
		Iterator it = charSet.iterator();
		int i = 0;
		while (it.hasNext()) {
			ret.add(it.next().toString());
			i++;
		}
		Collections.sort(ret);
		return ret;
	}
}