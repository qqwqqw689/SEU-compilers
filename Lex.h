#include <fstream>
#include <vector>
#include <deque>
#include <string>
#include <map>
#include <array>
using std::ifstream;
using std::ofstream;
using std::vector;
using std::deque;
using std::array;
using std::map;
using std::string;

int ParseLexFile(ifstream& ifs, ofstream& ofs);

// Uncertain finite automata:
// The status set is all lines of Ntran
// Input the alphabet as ASCII characters (129 columns with ε)
// Convert function to member Ntran
// The start state is the first line of Ntran
// The accept state is the last line of Ntran
class NFA{
public:
	typedef array<vector<size_t>, 129> NST;	// Each row in the NFA state table: Transitions to other states.
											// Each row contains 129 vectors
											// Represents a successor collection on 128 ASCII and epsilon
											// There is no duplication when adding, and it is more efficient to add 
											// and change things using vector instead of set
	NFA() {
		Ntran.push_back(NST());
	}
	NFA(char ch);
	inline size_t get_size()const { return Ntran.size(); }
	void opt_union(const NFA&);
	void opt_concat(const NFA&);
	void opt_star();
	void opt_plus();
	void opt_quest();
	vector<size_t> merge_nfa(const vector<NFA>&);
	vector<size_t> epsilon_closure(size_t s)const;
	vector<size_t> epsilon_closure(const vector<size_t>& ss)const;
	vector<size_t> move(const vector<size_t>& ss, char a)const;
	~NFA() {}
private:
	deque<NST> Ntran;		// Set of states (faster random access and double end add/delete with deque)
};

// Deterministic finite automata:
// The state set is all lines of Dtran
// Enter the alphabet as ASCII characters (128 columns)
// Convert function to member Dtran
// The first line of Dtran when the start state
// The acceptance status is reflected in the member accepts
class DFA {
public:
	typedef array<size_t, 128> DST;		// Each row in the DFA state table: Transitions to other states
										// Each row contains 128 size t
										// Represents the successor on 128 ASCII, with none for empty
	DFA(const NFA& , const vector<size_t>& );
	// DFA(const NFA& , size_t );
	inline size_t get_size()const { return Dtran.size(); }
	inline size_t get_tran(size_t i, size_t ch)const { return Dtran[i][ch]; }
	inline const vector<size_t> get_accepts()const { return accepts; }
	void minimize();
	void delete_dead_states();
private:
	vector<DST> Dtran;				// state transition
	vector<size_t> accepts;			// The mode number corresponds to the accepted state, and the mode number corresponds to -1 for the non-accepted state

	DST newDST() {					// -1 indicates no conversion
		DST st;
		for (size_t& i : st) {
			i = -1;
		}
		return st;
	}
};