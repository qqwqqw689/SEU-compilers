#include <iostream> // For debug.
#include <fstream>
#include <string>
#include <vector>
#include <map>
#include <stack>
#include <set>
#include <array>
#include <list>
#include "Lex.h"

using namespace std;

// A special char is used to represent morphemes in regular expressions,
// where the highest bit is 1 is an operator, otherwise it is an operand

// Operand to operator
// 0x80 <=> 0b10000000
inline char to_operator(char ch)
{
	return ch | 0x80;
}

// int(to_operator('(') <=> -88
// int(to_operator(')') <=> -87
// int(to_operator('|') <=> -4
// int(to_operator('.') <=> -82
// int(to_operator('{') <=> -5
// int(to_operator('}') <=> -3
// int(to_operator('*') <=> -86

// Operator to operand
// 0x7f <==> 0b01111111
inline char to_char(char ch)
{
	return ch & 0x7f;
}
// Determines whether it is an operator
inline bool is_optr(char ch)
{
	return ch & 0x80;
}

// Definition of NFA

// Single character to NFA
NFA::NFA(char ch)
{
	NST s0, s1;
	s0[(size_t)ch].push_back(1);
	Ntran.push_back(s0);
	Ntran.push_back(s1);
}

// Thompson: union
void NFA::opt_union(const NFA &rhs)
{ // Fetch union
	size_t x = get_size();
	size_t y = rhs.get_size();
	Ntran.pop_back(); // Deletes the original accept state
	for (auto &s : Ntran)
	{ 	// The accept state is the last line of Ntran.
		// All transitions to the original accept state are then 
		// changed to the new accept state x + y - 3 ((x-1)+(y-1)-1)
		for (auto &t : s)
		{
			for (auto &spt : t)
			{
				if (spt == x - 1)
				{
					spt = x + y - 3;
				}
			}
		}
	}
	// Merge the states of the right
	// automaton except for state 0 (conversion followed by all + (x-2))
	for (size_t i = 1; i < y; ++i)
	{
		Ntran.push_back(rhs.Ntran[i]);
	}
	for (size_t i = x - 1; i < x + y - 2; ++i)
	{
		for (auto &t : Ntran[i])
		{
			for (auto &spt : t)
			{
				spt += x - 2;
			}
		}
	}
	// Merge the state 0 information of the right
	// automaton (conversion followed by all + (x-2))
	for (size_t ch = 0; ch < 129; ++ch)
	{
		for (auto t : rhs.Ntran[0][ch])
		{
			Ntran[0][ch].push_back(t + x - 2);
		}
	}
}
// Thompson: concatenate
void NFA::opt_concat(const NFA &rhs)
{ // concatenate
	size_t x = get_size();
	size_t y = rhs.get_size();
	Ntran.pop_back(); // Deletes the original accept state
	for (auto s : rhs.Ntran)
	{ // Add all the right automaton states to the left
		Ntran.push_back(s);
	}
	for (size_t i = x - 1; i < x + y - 1; ++i)
	{
		for (auto &t : Ntran[i])
		{
			for (auto &spt : t)
			{
				spt += x - 1;
			}
		}
	}
}

// Thompson: closure
void NFA::opt_star()
{ // closure
	NST oldNtran0 = Ntran[0];
	Ntran.pop_front();
	Ntran.push_front(NST());							   // New start state 0
	Ntran[0][128].push_back(Ntran.size() - 1);			   // Set the epsilon transition from 0 state to accepted state
	*(Ntran.end() - 1) = oldNtran0;						   // Set the transition from the accept state to itself (same as the original 0 state)
	Ntran.push_back(NST());								   // Add a new end state x
	(*(Ntran.end() - 2))[128].push_back(Ntran.size() - 1); // Set the epsilon transition from the X-1 state to the x state
}
// Thompson: positive closure
void NFA::opt_plus()
{ // positive closure
	// This is equivalent to a & a*
	NFA cp = *this;
	cp.opt_star();
	opt_concat(cp);
}
// Thompson: question mark
void NFA::opt_quest()
{ // 0 or 1
	// Add an epsilon transition from the initial state to the accepted state
	Ntran[0][128].push_back(Ntran.size() - 1);
}
// A series of Nfas are merged to return the sequence number of the accepted states,
// that is, the accepted state corresponding to the I-th automaton is stored in the I-th position
vector<size_t> NFA::merge_nfa(const vector<NFA> &nfas)
{
	vector<size_t> accepts;
	Ntran.clear();
	Ntran.push_back(NST()); // Create a new NFA with only the start state
	size_t offset = 1;
	for (auto nfa : nfas)
	{
		Ntran[0][128].push_back(offset); // epsilon transition from new state 0 to the initial state of the automaton to be merged
		size_t size = nfa.get_size();
		for (auto s : nfa.Ntran)
		{
			Ntran.push_back(s); // Adds all states of the automaton to be merged
		}
		for (size_t i = 0; i < size; ++i)
		{
			for (auto &t : Ntran[i + offset])
			{
				for (auto &spt : t)
				{
					spt += offset; // Status number plus offset
				}
			}
		}
		offset += size;
		accepts.push_back(offset - 1); // add accept state
	}
	return accepts;
}

// Find an epsilon closure of a state
vector<size_t> NFA::epsilon_closure(size_t s) const
{
	vector<size_t> tmp{s};
	return epsilon_closure(tmp);
}
// Find the epsilon closure of a set of states
vector<size_t> NFA::epsilon_closure(const vector<size_t> &ss) const
{
	set<size_t> resSet(ss.begin(), ss.end()); // Initialize the resSet with ss
	stack<size_t, vector<size_t>> stk(ss);	  // Initialize the stack with ss
	while (!stk.empty())
	{
		size_t t = stk.top();
		stk.pop();
		for (size_t u : Ntran[t][128])
		{
			if (!resSet.count(u))
			{
				resSet.insert(u);
				stk.push(u);
			}
		}
	}
	vector<size_t> res; // The result is converted to a vector only for the convenience of function calls
	for (size_t i : resSet)
	{ // Note that the returned vector must be sorted
		res.push_back(i);
	}
	return res;
}

// move function that finds a set of states (the result of this function is
// not a set, may have duplicate elements, but is always used along with epsilon closures)
vector<size_t> NFA::move(const vector<size_t> &ss, char a) const
{
	vector<size_t> res;
	vector<size_t> ec = epsilon_closure(ss);
	for (size_t s : ec)
	{
		for (size_t d : Ntran[s][(size_t)a])
		{
			res.push_back(d);
		}
	}
	return res;
}

// Definition of DFA

// Initialize the DFA with the merged NFA (multiple accept states)
DFA::DFA(const NFA &nfa, const vector<size_t> &nacn)
{

	vector<vector<size_t>> Dstates; // Each state of the DFA corresponds to a set of states of the NFA
	stack<size_t> unFlaged;			// Unmarked DFA status

	Dstates.push_back(nfa.epsilon_closure(0)); // Dstates started with epsilon-closure(s0)
	Dtran.push_back(newDST());				   // Add a state to Dtran
	unFlaged.push(0);						   // And not marked

	while (!unFlaged.empty())
	{
		size_t Tidx = unFlaged.top(); // Retrieves an unmarked DFA state
		unFlaged.pop();
		size_t Uidx = 0;
		vector<size_t> T = Dstates[Tidx]; // The corresponding set of NFA states
		for (size_t a = 0; a < 128; ++a)
		{
			vector<size_t> U = nfa.epsilon_closure(nfa.move(T, (char)a));
			if (!U.empty())
			{ // There is a conversion
				bool UinDstates = false;
				for (size_t i = 0; i < Dstates.size(); ++i)
				{ // Determine whether U is in Dstates
					if (U == Dstates[i])
					{ 	// Because the results of the functions that evaluate epsilon
						// closures are all sorted, they can be directly compared
						UinDstates = true;
						Uidx = i;
						break;
					}
				}
				if (!UinDstates)
				{							   // U is not in Dstates
					Dstates.push_back(U);	   // add into Dstates
					Dtran.push_back(newDST()); // Add a state to Dtran
					Uidx = Dstates.size() - 1;
					unFlaged.push(Uidx); // And not marked
				}
				Dtran[Tidx][(size_t)a] = Uidx;
			}
		}
	}

	for (size_t i = 0; i < Dstates.size(); ++i)
	{							 // Determine whether the DFA status is accepted
		size_t firstAccept = -1; // Takes the first listed pattern corresponding to the accepted state
		for (auto s : Dstates[i])
		{
			if (nacn[s] != -1)
			{
				// -1 + size_t => very very large
				firstAccept = nacn[s] < firstAccept ? nacn[s] : firstAccept;
			}
		}
		accepts.push_back(firstAccept);
	}
}

// minimize DFA
void DFA::minimize() {
	vector<size_t> sttGroup(get_size());	// The group to which the status belongs
	vector<set<size_t>> grpStates;			// What states are in each group
	size_t maxAccNum = 0;					// Maximum acceptance status number
	for (auto n : accepts) {
		if (n != -1) {
			maxAccNum = n > maxAccNum ? n : maxAccNum;
		}
	}
	for (size_t i = 0; i < maxAccNum + 2; ++i) {	// Initially, there are maxAccNum + 2 groups
													// Corresponding to maxAccNum + 1 different accept status groups
													// And 1 other status group
		grpStates.push_back(set<size_t>());
	}
	for (size_t i = 0; i < get_size(); ++i) {
		if (accepts[i] == -1) {				// The state of non-acceptance
			sttGroup[i] = maxAccNum + 1;
			grpStates[maxAccNum + 1].insert(i);
		}
		else {
			sttGroup[i] = accepts[i];
			grpStates[accepts[i]].insert(i);
		}
	}
	bool modified = false;
	do {
		modified = false;
		for (auto g : grpStates) {
			if (g.size() == 1) {					// If there is only one state in the group, it is not considered
				continue;
			}
			else {
				vector<size_t> helper;
				set<size_t>::iterator begin = g.begin();
				for (set<size_t>::iterator s = g.begin(); s != g.end(); ++s) {
					if(s == begin)
						continue;
					if(!modified) {
						for (size_t ch = 0; ch < 128; ++ch) {
							if ((Dtran[*begin][ch] != Dtran[*s][ch])&&(sttGroup[Dtran[*begin][ch]] != sttGroup[Dtran[*s][ch]])) {
								modified = true;
								helper.push_back(*s);
							}
						}
					}
					else {
						size_t a = helper[0];
						bool In_The_Same_Group = true;
						for (size_t ch = 0; ch < 128; ++ch) {
							if ((Dtran[*begin][ch] != Dtran[*s][ch])&&(sttGroup[Dtran[*begin][ch]] != sttGroup[Dtran[*s][ch]])) {
								In_The_Same_Group = false;
							}
						}
						if(In_The_Same_Group)
							helper.push_back(*s);
					}
				}
				set<size_t> newset;
				if(helper.size() != 0) {
					for(auto a: helper) {
						g.erase(a);
						sttGroup[a] = grpStates.size();
						newset.insert(a);
					}
					grpStates.push_back(newset);
				}
			}
		}
	} while (modified);

	size_t newstatessize = grpStates.size();

	vector<DST> newDtran;
	int size = grpStates.size();
	stack<size_t> unFlaged;
	newDtran.push_back(newDST());
	unFlaged.push(0);

	while (!unFlaged.empty()) {
		size_t Tidx = unFlaged.top();
		unFlaged.pop();
		int i;
		for(i=0; i < sttGroup.size(); i++)
			if(sttGroup[i] == Tidx)
				break;
		for (size_t a = 0; a < 128; ++a)
		{
			int trans = Dtran[i][a];
			
		}
	}
}

// Delete dead state
void DFA::delete_dead_states() {
	for (size_t i = 0; i < get_size(); ++i) {
		if (accepts[i] != -1) {				// accept state, skip.
			continue;
		}
		else {
			
		}
	}
}

// Determine whether ch is a character that must be escaped in a regular expression
// Regular expressions use the backslash character ('\') to indicate special forms or
// to allow special characters to be used without invoking their special meaning.
// For example, In lex files, the backslash followed by a question mark (?) is typically
// used to match a literal question mark character (?).
inline bool need_escape(char ch)
{
	if (ch == '\\' || ch == '\"' || ch == '.' || ch == '^' || ch == '$' || ch == '[' || ch == ']' || ch == '*' || ch == '+' || ch == '?' || ch == '{' || ch == '}' || ch == '|' || ch == '/' || ch == '(' || ch == ')')
	{
		return true;
	}
	else
	{
		return false;
	}
}

// Determines whether it is an operator, i.e. a backslash that
// previously had no real meaning (an even number of consecutive backslashes)
inline bool is_not_escaped(string::const_iterator it, const string &str)
{
	if (it == str.begin())
	{
		return true;
	}
	else
	{
		it--;
		int backSlashCount = 0;
		for (; it != str.begin(); --it)
		{
			if (*it == '\\')
			{
				++backSlashCount;
			}
			else
			{
				break;
			}
		}
		if (backSlashCount % 2 == 0)
		{
			return true;
		}
		else
		{
			return false;
		}
	}
}

// Analyzes two parts of a line separated by tabs.
pair<string, string> split_by_blank(const string &str)
{
	bool flag = true;
	string name, expr;
	for (auto c : str)
	{
		if (flag)
		{
			if (c != '\t')
			{
				name.push_back(c);
			}
			else
			{
				flag = false;
			}
		}
		else
		{
			if (c != '\t')
			{
				expr.push_back(c);
			}
			else
			{
				if (expr.empty())
					continue;
				else
					break;
			}
		}
	}
	return pair<string, string>(name, expr);
}

// "." is just a point
// . is a operator

// Parses a regular expression string into a sequence of symbols and handles parentheses and quotes
vector<char> deal_brkt_qt(const string &exp)
{

	vector<char> res;
	string inBracket;			 // The actual character in the bracket([])
	bool bracketFlag = false;	 // Detection bracket
	bool notBracketFlag = false; // Detection bracket（Complement form）
	bool quotationFlag = false;	 // Detection quotes

	// const_iterator
	// dereferencing converts the value returned by the underlying iterator as immutable.
	for (string::const_iterator it = exp.begin(); it != exp.end(); ++it)
	{
		// Enter quotes, and inside brackets do not count
		if (!quotationFlag && !bracketFlag && !notBracketFlag && *it == '\"' && is_not_escaped(it, exp))
		{
			quotationFlag = true;
		}
		// End of quote
		else if (quotationFlag && !bracketFlag && !notBracketFlag && *it == '\"' && is_not_escaped(it, exp))
		{
			quotationFlag = false;
		}
		// Inside quotation("") marks
		else if (quotationFlag)
		{
			res.push_back(*it);
		}
		// enter bracket ([]).
		else if (!bracketFlag && !notBracketFlag && *it == '[' && is_not_escaped(it, exp))
		{
			// the caret symbol (^)
			// This operator is used to match any character
			// except the ones specified following the caret.
			if (*(it + 1) != '^')
			{
				bracketFlag = true;
			}
			else
			{
				++it;
				notBracketFlag = true;
			}
			inBracket.clear();
		}
		// End of bracket
		else if (bracketFlag && *it == ']' && is_not_escaped(it, exp))
		{
			bracketFlag = false;
			res.push_back(to_operator('('));
			bool first = true;
			for (auto c = inBracket.begin(); c != inBracket.end(); ++c)
			{
				if (first)
				{ // Add | between all but the first
					first = false;
				}
				else
				{
					res.push_back(to_operator('|'));
				}
				if (*c == '\\')
				{ // If it is escaped, the escaped symbol is viewed as a whole
					if (need_escape(*(++c)))
					{
						res.push_back(*c);
					}
					else
					{
						switch (*c)
						{
						case 'a':
							res.push_back('\a'); // alert (bell) character.
							break;
						case 'b':
							res.push_back('\b'); // backspace character
							break;
						case 'f':
							res.push_back('\f'); // feed character
							break;
						case 'n':
							res.push_back('\n'); // newline character
							break;
						case 'r':
							res.push_back('\r'); // carriage return character
							break;
						case 't':
							res.push_back('\t'); // horizontal tab character
							break;
						case 'v':
							res.push_back('\v'); // vertical tab character
							break;
						}
					}
				}
				else
				{
					res.push_back(*c);
				}
			}
			res.push_back(to_operator(')'));
		}
		// End of bracket (Complement form)
		else if (notBracketFlag && *it == ']' && is_not_escaped(it, exp))
		{
			notBracketFlag = false;
			res.push_back(to_operator('('));
			bool allChar[128];
			// Calculation of the complement: Set the bool value of the
			// corresponding position of all characters in the original set to 0
			for (size_t i = 0; i < 128; ++i)
			{
				allChar[i] = true;
			}
			for (auto c = inBracket.begin(); c != inBracket.end(); ++c)
			{
				if (*c == '\\')
				{
					if (need_escape(*(++c)))
					{
						allChar[(size_t)(*c)] = false;
					}
					else
					{
						switch (*c)
						{
						case 'a':
							allChar[(size_t)'\a'] = false;
							break;
						case 'b':
							allChar[(size_t)'\b'] = false;
							break;
						case 'f':
							allChar[(size_t)'\f'] = false;
							break;
						case 'n':
							allChar[(size_t)'\n'] = false;
							break;
						case 'r':
							allChar[(size_t)'\r'] = false;
							break;
						case 't':
							allChar[(size_t)'\t'] = false;
							break;
						case 'v':
							allChar[(size_t)'\v'] = false;
							break;
						}
					}
				}
				else
				{
					allChar[(size_t)(*c)] = false;
				}
			}
			bool first = true;
			for (size_t i = 0; i < 128; ++i)
			{
				if (allChar[i])
				{
					if (first)
					{
						first = false;
					}
					else
					{
						res.push_back(to_operator('|'));
					}
					char ch = (char)i;
					res.push_back(ch);
					// if (need_escape(ch)) {			// If you need to escape, add an escape symbol
					//	res.push_back(ch);
					// }
					// else {
					//
					//	res.push_back(ch);
					// }
				}
			}
			res.push_back(to_operator(')'));
		}
		// Inside the brackets, fill into the inBracket.
		else if (bracketFlag || notBracketFlag)
		{
			if (*it != '-' || *(it + 1) == ']')
			{
				inBracket.push_back(*it);
			}
			else
			{ // 0-9 => from 0 to 9.
				// *(it - 1) has been in inBracket.
				for (char ch = *(it - 1) + 1; ch < *(it + 1); ++ch)
				{
					inBracket.push_back(ch);
				}
			}
		}
		else
		{
			if (*it == '\\')
			{
				if (need_escape(*(++it)))
				{
					res.push_back(*it);
				}
				else
				{
					switch (*it)
					{
					case 'a':
						res.push_back('\a');
						break;
					case 'b':
						res.push_back('\b');
						break;
					case 'f':
						res.push_back('\f');
						break;
					case 'n':
						res.push_back('\n');
						break;
					case 'r':
						res.push_back('\r');
						break;
					case 't':
						res.push_back('\t');
						break;
					case 'v':
						res.push_back('\v');
						break;
					}
				}
			}
			else
			{
				if (need_escape(*it))
				{
					res.push_back(to_operator(*it));
				}
				else
				{
					res.push_back(*it);
				}
			}
		}
	}
	return res;
}

// Parse regular definitions according to map
vector<char> explain_defs(const vector<char> &rgx, const map<string, vector<char>> &mp)
{
	vector<char> res;
	bool braceFlag = false;
	string defName; // The used regular defines symbols
	for (vector<char>::const_iterator it = rgx.begin(); it != rgx.end(); ++it)
	{
		if (*it == to_operator('{') && !braceFlag)
		{
			braceFlag = true;
			defName.clear();
		}
		else if (*it == to_operator('}') && braceFlag)
		{
			braceFlag = false;
			if (mp.count(defName) == 0)
			{
			} // Maybe an error?
			else
			{
				res.push_back(to_operator('('));
				for (auto c : mp.at(defName))
				{
					res.push_back(c);
				}
				res.push_back(to_operator(')'));
			}
		}
		else if (braceFlag)
		{
			defName.push_back(*it);
		}
		else
		{
			res.push_back(*it);
		}
	}
	return res;
}

//

// Processing point
vector<char> deal_dot(const vector<char> &seq)
{
	vector<char> res;
	for (vector<char>::const_iterator it = seq.begin(); it != seq.end(); ++it)
	{
		// (Dot.) In the default mode, this matches any character except a newline.
		if (*it == to_operator('.'))
		{
			res.push_back(to_operator('('));
			bool first = true;
			for (unsigned i = 0; i < 128; ++i)
			{
				if (i != '\n')
				{
					if (first)
					{
						first = false;
						res.push_back((char)i);
					}
					else
					{
						res.push_back(to_operator('|'));
						res.push_back((char)i);
					}
				}
			}
			res.push_back(to_operator(')'));
		}
		else
		{
			res.push_back(*it);
		}
	}
	return res;
}

// /* => /&*
// struct => s&t&r&u&c&t
// 0(x|X)((a-fA-F0-9))+(((u|U)|(u|U)?(l|L|ll|LL)|(l|L|ll|LL)(u|U)))? =>
// 0&(x|X)&((a-fA-F0-9))+&(((u|U)|(u|U)?&(l|L|l&l|L&L)|(l|L|l&l|L&L)&(u|U)))?

// Add a connector (to operator('&'), in the form of an operator)
vector<char> seq_to_infix(const vector<char> &seq)
{
	vector<char> res;
	bool pre = false;
	for (vector<char>::const_iterator it = seq.begin(); it != seq.end(); ++it)
	{
		if (pre)
		{
			if (!is_optr(*it) || to_char(*it) == '(')
			{
				res.push_back(to_operator('&'));
				res.push_back(*it);
			}
			else
			{
				res.push_back(*it);
			}
		}
		else
		{
			res.push_back(*it);
		}
		if (!is_optr(*it) || to_char(*it) == ')' || to_char(*it) == '*' || to_char(*it) == '+' || to_char(*it) == '?')
		{
			pre = true;
		}
		else
		{
			pre = false;
		}
	}
	return res;
}

// 0&(x|X)&((a-fA-F0-9))+&(((u|U)|(u|U)?&(l|L|l&l|L&L)|(l|L|l&l|L&L)&(u|U)))? =>
// 0xX|&ab|c|d|e|f|A|B|C|D|E|F|0|1|2|3|4|5|6|7|8|9|+&uU|uU|?lL|ll&|LL&|&|lL|ll&|LL&|uU|&|?&

// Converts an infix regular expression to a suffix regular expression
vector<char> infix_to_suffix(const vector<char> &seq)
{
	vector<char> res;
	stack<char> optrStk;
	map<char, int> priority{
		{'*', 7},
		{'+', 7},
		{'?', 7},
		{'&', 5},
		{'|', 3}};
	for (vector<char>::const_iterator it = seq.begin(); it != seq.end(); ++it)
	{
		if (!is_optr(*it))
		{
			res.push_back(*it);
		}
		else
		{
			if (*it == to_operator('('))
			{
				optrStk.push(*it);
			}
			else if (*it == to_operator(')'))
			{
				while (!optrStk.empty() && to_char(optrStk.top()) != '(')
				{
					res.push_back(optrStk.top());
					optrStk.pop();
				}
				if (!optrStk.empty())
				{
					optrStk.pop();
				}
			}
			else
			{
				if (optrStk.empty() || to_char(optrStk.top()) == '(')
				{
					optrStk.push(*it);
				}
				else
				{
					if (priority[to_char(*it)] > priority[to_char(optrStk.top())])
					{
						optrStk.push(*it);
					}
					else
					{
						while (!optrStk.empty() && priority[to_char(*it)] <= priority[to_char(optrStk.top())])
						{
							res.push_back(optrStk.top());
							optrStk.pop();
						}
						optrStk.push(*it);
					}
				}
			}
		}
	}
	while (!optrStk.empty())
	{
		res.push_back(optrStk.top());
		optrStk.pop();
	}
	return res;
}

// Convert the suffix expression to NFA
NFA suffix_to_nfa(const vector<char> &seq)
{
	stack<NFA> s;
	for (vector<char>::const_iterator it = seq.begin(); it != seq.end(); ++it)
	{
		if (!is_optr(*it))
		{
			s.push(NFA(to_char(*it)));
		}
		else
		{
			if (to_char(*it) == '|')
			{
				NFA rhs = s.top();
				s.pop();
				NFA lhs = s.top();
				s.pop();
				lhs.opt_union(rhs);
				s.push(lhs);
			}
			else if (to_char(*it) == '&')
			{
				NFA rhs = s.top();
				s.pop();
				NFA lhs = s.top();
				s.pop();
				lhs.opt_concat(rhs);
				s.push(lhs);
			}
			else if (to_char(*it) == '*')
			{
				NFA lhs = s.top();
				s.pop();
				lhs.opt_star();
				s.push(lhs);
			}
			else if (to_char(*it) == '+')
			{
				NFA lhs = s.top();
				s.pop();
				lhs.opt_plus();
				s.push(lhs);
			}
			else if (to_char(*it) == '?')
			{
				NFA lhs = s.top();
				s.pop();
				lhs.opt_quest();
				s.push(lhs);
			}
			else
			{
			}
		}
	}
	return s.top();
}

void gen_code(ofstream &ofs, const DFA &dfa, const vector<string> &actions)
{
	const vector<size_t> accepts = dfa.get_accepts();
	ofs << "unsigned tran[][128] = {\n";
	for (size_t i = 0; i < dfa.get_size(); ++i)
	{
		ofs << '\t' << "{\t";
		for (size_t ch = 0; ch < 128; ++ch)
		{
			ofs << dfa.get_tran(i, ch);
			if (ch != 127)
			{
				ofs << ',';
			}
			ofs << '\t';
		}
		ofs << '}';
		if (i != dfa.get_size() - 1)
		{
			ofs << ',';
		}
		ofs << '\n';
	}
	ofs << "};\n\n";
	ofs << "int yylex() {\n";
	ofs << '\t' << "while (*p) {\n";
	ofs << '\t' << '\t' << "if (*p == '\\n')\t++line;\n";
	ofs << '\t' << '\t' << "char *forward = p;\n";
	ofs << '\t' << '\t' << "unsigned lastAccept = -1;\n";
	ofs << '\t' << '\t' << "unsigned stateNum = 0;\n";
	ofs << '\t' << '\t' << "for (int i = 0; *forward; ++i) {\n";
	ofs << '\t' << '\t' << '\t' << "stateNum = tran[stateNum][(unsigned)*forward];\n";
	ofs << '\t' << '\t' << '\t' << "if (stateNum == -1) {\n";
	ofs << '\t' << '\t' << '\t' << '\t' << "break;\n";
	ofs << '\t' << '\t' << '\t' << "}\n";
	ofs << '\t' << '\t' << '\t' << "else if (stateNum == ";
	bool first = true;
	for (size_t i = 0; i < accepts.size(); ++i)
	{
		if (accepts[i] != -1)
		{
			if (first)
			{
				first = false;
			}
			else
			{
				ofs << " || stateNum == ";
			}
			ofs << i;
		}
	}
	ofs << ") {\n";
	ofs << '\t' << '\t' << '\t' << '\t' << "lastAccept = stateNum;\n";
	ofs << '\t' << '\t' << '\t' << "}\n";
	ofs << '\t' << '\t' << '\t' << "++forward;\n";
	ofs << '\t' << '\t' << "}\n";
	ofs << '\t' << '\t' << "yytextlen = forward - p;\n";
	ofs << '\t' << '\t' << "int i = 0;\n";
	ofs << '\t' << '\t' << "for (; i < yytextlen; ++i) {\n";
	ofs << '\t' << '\t' << '\t' << "yytext[i] = p[i];\n";
	ofs << '\t' << '\t' << "}\n";
	ofs << '\t' << '\t' << "yytext[i] = '\\0';\n";
	ofs << '\t' << '\t' << "p = forward;\n";
	ofs << '\t' << '\t' << "switch (lastAccept) {\n";
	for (size_t i = 0; i < accepts.size(); ++i)
	{
		if (accepts[i] != -1)
		{
			ofs << '\t' << '\t' << "case " << i << ":\n";
			ofs << '\t' << '\t' << '\t' << actions[accepts[i]] << '\n';
			ofs << '\t' << '\t' << '\t' << "break;\n";
		}
	}
	ofs << '\t' << '\t' << "}\n";
	ofs << '\t' << "}\n";
	ofs << '\t' << "printf(\"unexpected eof\");\n";
	ofs << '\t' << "return 0;\n";
	ofs << "}\n\n";
}

// Parse the lex file, generate a lexer, and return the error line number
int ParseLexFile(ifstream &ifs, ofstream &ofs)
{

	vector<string> names;		// Regular definition - name (corresponding to defined index)
	vector<string> definitions; // Regular definition - definition (corresponding to name index)
	vector<string> rules;		// Rules (corresponding to action index)
	vector<string> actions;		// Action (corresponding to rule index)
	string toCopy;				// copy part
	string subRout;				// Subroutine part

	// Analyze files to variables

	{
		vector<string> allLines; // Store all rows
		string line;			 // current row
		int lineCount = 0;		 // line number
		vector<int> lineTypes;	 // Attributes of marked rows:
		int line_type = 0;		 // 1：Regular expression part
								 // 2：Rule part
								 // 3：Copy part
								 // 4：Subroutine part

		/*
		definitions
		%%
		rules
		%%
		user subroutines
		*/

		while (getline(ifs, line))
		{ // First find two %% and divide the file into three parts
			if (line.empty())
				continue;
			++lineCount;
			allLines.push_back(line);
			lineTypes.push_back(line_type);
			if (line.compare("%%") == 0)
			{
				if (line_type == 0)
				{
					line_type = 2;
				}
				else if (line_type == 2)
				{
					line_type = 4;
					lineTypes.back() = 0;
				}
				else
					return lineCount; // we can have at most 2 %%.
			}
		}

		// Lines in the definitions section beginning with a blank or enclosed
		// in %{, %} delimiter lines are copied to the lex.yy.c file.
		bool regxFlag = true; // For the part before the first %%, analyze the code between %{and %}
		line_type = 1;
		for (size_t i = 0; i < lineTypes.size(); ++i)
		{
			if (regxFlag && lineTypes[i] == 2)
			{
				lineTypes[i - 1] = 0;
				regxFlag = false;
				continue;
			}
			if (regxFlag)
			{
				lineTypes[i] = line_type;
				if (allLines[i].compare("%{") == 0)
				{
					line_type = 3;
					lineTypes[i] = 0;
				}
				else if ((allLines[i].compare("%}") == 0) && line_type == 3)
				{
					line_type = 1;
					lineTypes[i] = 0;
				}
			}
		}

		for (size_t i = 0; i < allLines.size(); ++i)
		{
			switch (lineTypes[i])
			{
			case 1:
				names.push_back(split_by_blank(allLines[i]).first);
				definitions.push_back(split_by_blank(allLines[i]).second);
				break;
			case 2:
				rules.push_back(split_by_blank(allLines[i]).first);
				actions.push_back(split_by_blank(allLines[i]).second);
				break;
			case 3:
				toCopy.append(allLines[i]);
				toCopy.push_back('\n');
				break;
			case 4:
				subRout.append(allLines[i]);
				subRout.push_back('\n');
				break;
			}
		}

		// Post-processing: Write semantic actions on multiple lines
		// (i.e. semantically empty), concatenate them
		vector<string>::iterator last1 = rules.begin(), last2 = actions.begin();
		for (auto it1 = rules.begin(), it2 = actions.begin(); it1 != rules.end() && it2 != actions.end(); ++it1, ++it2)
		{
			if (*it1 == "")
			{ // if the string is empty.
				last2->append(*it2);
				it1 = rules.erase(it1);
				it2 = actions.erase(it2);
				it1--;
				it2--;
			}
			last1 = it1;
			last2 = it2;
		}
	}

	// Parse definitions and rules into sequences

	vector<vector<char>> defsSeq;
	for (auto d : definitions)
	{
		defsSeq.push_back(deal_brkt_qt(d));
	}
	// [0-9] => (0|1|2|3|4|5|6|7|8|9)

	vector<vector<char>> rulesSeq;
	for (auto r : rules)
	{
		rulesSeq.push_back(deal_brkt_qt(r));
	}
	// {D}*"."{D}+{E}?{FS}? =>
	// {D}*.{D}+{E}?{FS}?

	// Interpret nested definitions in regular definitions
	// (that is, the latter definition uses the contents of the previous definition),
	// and establish a mapping of names to definitions

	map<string, vector<char>> mapNameToDef;
	mapNameToDef.insert(pair<string, vector<char>>(names[0], defsSeq[0])); // First add.
	for (size_t i = 1; i < defsSeq.size(); ++i)
	{ // Subsequent definitions recursively use established mappings
		mapNameToDef.insert(pair<string, vector<char>>(names[i], explain_defs(defsSeq[i], mapNameToDef)));
	}

	// Explain regular definitions in regular expressions

	for (auto &pd : rulesSeq)
	{
		vector<char> npd = explain_defs(pd, mapNameToDef);
		pd = npd;
	}

	// {L}({L}|{D})* =>
	// ((a-zA-Z_))(((a-zA-Z_))|((0-9)))*

	// Convert all regular expressions to NFA

	vector<NFA> nfas;
	for (auto r : rulesSeq)
	{
		nfas.push_back(suffix_to_nfa(infix_to_suffix(seq_to_infix(deal_dot(r)))));
	}

	// Merge all Nfas, output the total NFA and accept the status number table.

	NFA mergedNFA;
	vector<size_t> NAcceptedStates = mergedNFA.merge_nfa(nfas);
	vector<size_t> Naccept(mergedNFA.get_size());
	for (auto &acn : Naccept)
	{
		acn = -1;
	}
	for (size_t i = 0; i < NAcceptedStates.size(); ++i)
	{
		Naccept[NAcceptedStates[i]] = i;
	}

	// Convert NFA to DFA, minimizing DFA

	DFA dfa(mergedNFA, Naccept);
	// dfa.minimize();
	// dfa.delete_dead_states();

	// Generate lexical analyzer source files according to DFA

	ofs << toCopy << '\n';
	gen_code(ofs, dfa, actions);
	ofs << subRout << '\n';

	return 0;
}