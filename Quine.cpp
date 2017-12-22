#include <iostream>
#include <iomanip>
#include <sstream>
#include <string>
#include <vector>
#include <algorithm>
#include <fstream>
using namespace std;

auto error(ofstream &out)->void {
	out << "error\n";
}


class QM;
class Implicant {
public:
	Implicant(int i = 0, int vars=0, vector<int> min = vector<int>(), int m = 0,bool used=false);
	vector<int> add_v_mint(const Implicant &b);
	bool operator<(const Implicant& b) const;
	auto get_minterm()->const int& { return implicant; };
	auto get_bits()-> const string&{ return bits; };
private:
	//ones - вес вектора в таблице истинности, вес минтермы
	//mask позволяет дешифровать место(а) нахождения (-) в полученном импликанте, т.к. представляет собой степень двойки
	//bits - двоичное представление минтермы или импликанта 
	//vars - количество переменных в таблице истинности
	//used - булева переменная. Изменяет свое значение, в случае если минтерм или импликант использовался в слиянии
	//mints - хранит минтермы , используемые при склеивании, например, для 00- = (m0,m1), mints ={0,1}
	int implicant, vars, mask, ones;
	string bits;
	vector<int> mints;
	bool used;
	friend ostream &operator<<(ostream &out, const Implicant &im);
	friend class QM;
};

Implicant::Implicant(int i, int vars, vector<int> min, int m,bool used) :implicant(i),mask(m),ones(0),vars(vars),used(used){
	(min.empty()) ? mints.push_back(i) : mints = min;
	int bit = 1 << vars;
	while (bit >>= 1)
		if (mask & bit) bits += '*';
		else if (implicant & bit) { bits += '1'; ++ones; }
		else bits += '0';

}

auto Implicant::add_v_mint(const Implicant &b)->vector<int> {
	vector<int> v = this->mints;
	v.insert(v.end(), b.mints.begin(), b.mints.end());
	return v;
}

auto Implicant::operator<(const Implicant& b) const->bool{
	return this->ones < b.ones;
}

ostream &operator<<(ostream &out, const Implicant &im) {
	int bit = 1 << im.vars, lit = 0;
	ostringstream ss;
	while (bit >>= 1) {
		if (!(im.mask & bit))
			ss << char(lit + 'A') << (im.implicant & bit ? ' ' : '\'');
		++lit;
	}
	out << ss.str();
	return out;
}

//------------------------------------------------------------------------------------------------

class QM {
public:
	QM(int vars,vector<size_t> min, vector<Implicant> imp);
	auto solve()->void; 
	auto weight(size_t x)->int; //определяем вес вектора двоичного представления числа
	auto cover(vector<size_t> &a, const vector<size_t> &b)->void;
	auto get_flag()->const bool&;
	auto get_primes()->const vector<Implicant>&;
	auto get_M()-> const vector<size_t>&;
	auto get_ind()-> const int&;
private:
	int vars;//количество переменных в таблице истинности
	int comb;//высота таблицы истинности
	int ind;
	vector<size_t> minterms, M0;
	vector<Implicant> implicants,primes;
	bool flag;
};

QM::QM(int vars, vector<size_t> min,vector<Implicant> impl) :vars(vars), minterms(min), comb(1 << vars),implicants(impl),flag(true),ind(0) {
	sort(minterms.begin(),minterms.end());
	minterms.erase(unique(minterms.begin(), minterms.end()), minterms.end());
	sort(implicants.begin(), implicants.end());
	solve();
};

auto QM::weight(size_t x)->int {
	int k = 0;
	while (x) {
		k += x % 2;
		x >>= 1;
	}
	return k;
}

auto QM::get_flag()->const bool& {
	return flag;
}

auto QM::get_primes()-> const vector<Implicant>&{
	return primes;
}

auto QM::get_M()-> const vector<size_t>&{
	return M0;
}

auto QM::get_ind()-> const int& {
	return ind;
}

auto QM::cover(vector<size_t> &a, const vector<size_t> &b)->void{
	vector<size_t> v;

	for (size_t i = 0; i < a.size(); ++i)
		for (size_t j = 0; j < b.size(); ++j)
			v.push_back(a[i] | b[j]);
	sort(v.begin(), v.end());
	v.erase(unique(v.begin(), v.end()), v.end());

	for (size_t i = 0; i < v.size() - 1; ++i)
		for (size_t j = i+1; j < v.size(); ++j) {
			size_t z = v[i] & v[j];
			if (z == v[i])
				v.erase(v.begin() + j);
			else if (z == v[j]) {
				size_t t = v[i];
				v[i] = v[j];
				v[j] = t;
				v.erase(v.begin() + j);
				j = v.size();
			}
		}
	a = v;
}


auto QM::solve()->void {
	vector<Implicant> aux;
	
	while (implicants.size() > 1) {

		sort(implicants.begin(), implicants.end(),[](Implicant & a, Implicant & b) -> bool{
			return a.get_bits().compare(b.get_bits()) < 0; });

		auto last = std::unique(implicants.begin(), implicants.end(), 
			[](Implicant &lhs, Implicant &rhs) { 
				return (lhs.get_bits() == rhs.get_bits()) ? true : false; });
		implicants.resize(last-implicants.begin());

		aux.clear();
		for (size_t i = 0; i < implicants.size() - 1; ++i)
			for (size_t j = i + 1; j < implicants.size(); ++j)
				if (implicants[j].ones == implicants[i].ones + 1 &&
					implicants[j].mask == implicants[i].mask &&
					weight(implicants[i].implicant ^ implicants[j].implicant) == 1) { 
					implicants[i].used = true;
					implicants[j].used = true;
					aux.push_back(Implicant(implicants[i].implicant, vars,
						implicants[i].add_v_mint(implicants[j]),
						(implicants[i].implicant ^ implicants[j].implicant) | implicants[i].mask));
				}

		for (size_t i = 0; i < implicants.size(); ++i)
			if (!implicants[i].used) primes.push_back(implicants[i]);
		implicants = aux;
	}

	for (size_t i = 0; i < implicants.size(); ++i)
		primes.push_back(implicants[i]);

	// на этом этапе программы получили сокращенную ДНФ

	if (primes.back().mask == comb - 1) {
		flag = false; return;
	}

	sort(primes.begin(), primes.end());

	// находим минимальные ДНФ методом импликантной матрицы
	vector<vector<bool>> table(primes.size(), vector<bool>(minterms.size(), false));

	for (size_t i = 0; i < primes.size(); ++i)
		for (size_t j = 0; j < primes[i].mints.size(); ++j)
			for (size_t k = 0; k < minterms.size(); ++k)
				if (primes[i].mints[j] == minterms[k])
					table[i][k] = true;

	vector<size_t> M1;
	for (size_t i = 0; i < primes.size(); ++i)
		if (table[i][0]) 
			M0.push_back(1 << i);
	
	for (int k = 1; k < minterms.size(); ++k) {
		M1.clear();
		for (int i = 0; i < primes.size(); ++i)
			if (table[i][k])
				M1.push_back(1 << i);
		
		cover(M0, M1);
	}

	
	int min = weight(M0[0]);
	for (size_t i = 1; i < M0.size(); ++i)
		if (min > weight(M0[i])) {
			min = weight(M0[i]);
			ind = i;
		}

}


auto out_solution(QM& in,ofstream &out)->void {
	if (in.get_flag()) {
		out << "F = ";
		bool f = false;
			for (size_t i = 0; i < in.get_primes().size(); ++i)
				if (in.get_M()[in.get_ind()] & (1 << i)) {
					if (f) out << " + ";
					f = true;
					out << in.get_primes()[i];
				}
			out << endl;
		}
	else
		out << "F = 1";
	}



int main(int argc, char* argv[])
{
	string s1(argv[1]);
	string s2(argv[2]);
	ifstream fin(s1);
	ofstream fout(s2);

	int vars,mint_size,temp;
	fin >> vars;
	if (vars < 1 || vars>9) { error(fout); return 0; }
	fin >> mint_size;
	if (mint_size<1 || mint_size>1<<vars) { error(fout); return 0; }
	vector<size_t> minterms;
	vector<Implicant> implicants;
	for (int i = 0; i < mint_size; i++) {
		fin >> temp;
		if (temp<0 || temp>(1<<vars) - 1) { error(fout); return 0; }
		minterms.push_back(temp);
		implicants.push_back(Implicant (temp,vars));
	}

	QM solution(vars,minterms,implicants);
	out_solution(solution,fout);

	fin.close();
	fout.close();
	return 0;
}
