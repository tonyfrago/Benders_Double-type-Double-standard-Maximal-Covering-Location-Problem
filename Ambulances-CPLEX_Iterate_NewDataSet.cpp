#include <ilcplex/ilocplex.h>
#include <time.h>
#include <vector>
#include <sstream>
#include <string>
#include <random>
//#include <iostream>
ILOSTLBEGIN

//-------------Global Variables--------------
int i, j, n, l;
const int imax = 625;
const int jmax = 625;
const int nmax = 1;
int Case;
int Example;


const int Big_M = 10000000;
double Importance_i[imax];
double Distance_ij[imax][jmax];
int Cv_ij[imax][jmax];
int Cm_ij[imax][jmax];
double P_m = 1;
double P_v = 0;
double Weight = 0;
double Budget = 0;
double v_standard = 0;
double m_standard = 5;
int BudgetParam = 10;


//Parameters affecting solution
double epsilon = 0.001;
double MaxTimeInSeconds = 3600;
int loop = 0;
int MaxIterations = 5000;
double UpperBound;
double LowerBound;
double LowerBoundGlobal;
double Gap;
double fraction = 0.90;
long double duration;  // tracks time
int start = 0, BDFeasCuts = 0, BDOptCuts = 0, CutsPerIteration, NoOfMasterVars, NoOfPrimalSlaveVars, NoOfDualSlaveVars, NoOfMasterCons, NoOfPrimalSlaveCons, NoOfDualSlaveCons;
int status_dual[imax];

double X_vjValue[jmax];
double X_mjValue[jmax];
double Y_vijValue[imax][jmax];
double Y_mijValue[imax][jmax];
double Lamda1_iValue[imax];
double Lamda2_iValue[imax];
double Beta_ijValue[imax][jmax];
double Gamma_ijValue[imax][jmax];
double ThetaValue = 0;

double OptimalX_vjValue[jmax];
double OptimalX_mjValue[jmax];
double OptimalY_vijValue[imax][jmax];
double OptimalY_mijValue[imax][jmax];
double OptimalLamda1_iValue[imax];
double OptimalLamda2_iValue[imax];
double OptimalBeta_ijValue[imax][jmax];
double OptimalGamma_ijValue[imax][jmax];
double OptimalThetaValue = 0;

double OriginalObjFunction = 0;
double MasterObjFunction = 0;
double PrimalSlaveObjFunction = 0;
double DualSlaveObjFunction = 0;

double OptimalOriginalObjFunction = 0;
double OptimalMasterObjFunction = 0;
double OptimalPrimalSlaveObjFunction = 0;
double OptimalDualSlaveObjFunction = 0;


//--------Construct Matrices----------------
typedef IloArray<IloNumArray> IloNumMatrix2x2;
typedef IloArray<IloNumMatrix2x2> IloNumMatrix3x3;
typedef IloArray<IloNumMatrix3x3> IloNumMatrix4x4;

typedef IloArray<IloNumVarArray> IloNumVarMatrix2x2;
typedef IloArray<IloNumVarMatrix2x2> IloNumVarMatrix3x3;
typedef IloArray<IloNumVarMatrix3x3> IloNumVarMatrix4x4;

typedef IloArray<IloRangeArray> IloRangeMatrix2x2;
typedef IloArray<IloRangeMatrix2x2> IloRangeMatrix3x3;
typedef IloArray<IloRangeMatrix3x3> IloRangeMatrix4x4;



vector <double> LowerBoundArray;
vector <double> UpperBoundArray;
vector <double> LowerBoundGlobalArray;
vector <double> dTy;
vector <double> zCurrent;
vector <double> cTx;
vector <double> bTu;
vector <double> BestPrimalSlaveObjSoFar;
vector <double> BestDualSlaveObjSoFar;
vector <double> Time;
vector <double> SlackValuesOfBendersCuts;
vector <double> SlackValuesOfMainMasterCons;
vector <double> NoOfCutsInEachIteration;
vector <double> NoOfCoveredVarsInEachIteration;


typedef struct treenode_tag {
	double  lpbound;  // LP bound
	IloModel  lp;     // ptr to master
	IloModel  lp_cg;   // ptr to colgen
	treenode_tag* nextnode;  // link to next node in tree
} treenode;

treenode_tag* BBTreeList;

void Found_Error(char* name)
{
	printf("%s failed, exiting...\n", name);
	printf("Press return to continue...\n");
	getchar();
}
int load_data() {
	string read_file = "";
	double max_Cij_Dij = 0;
	double product_I_Cij_Dij = 0;
	int X_Coordinate[imax], Y_Coordinate[imax];
	int index = 0;
	NoOfPrimalSlaveVars = imax * jmax * 2;
	NoOfDualSlaveVars = imax * jmax * 2 + imax * 2;
	NoOfPrimalSlaveCons = imax * jmax * 2 + imax * 2;
	NoOfDualSlaveCons = imax * jmax * 2;

	if (Case == 1) {
		v_standard = 2;
		P_v = 2;
		//m_standard = 5;
		//BudgetParam = 200;
	}
	else if (Case == 2) {
		v_standard = 3;
		P_v = 3;
		//m_standard = 5;
		//BudgetParam = 200;
	}
	else {
		v_standard = 4;
		P_v = 4;
		//m_standard = 5;
		//BudgetParam = 200;
	}


	//-------------------Declare Data of the problem--------------------
	for (i = 0; i < imax; i++) {
		Importance_i[i] = 0;
		for (j = 0; j < jmax; j++) {
			Distance_ij[i][j] = 0;
			Cv_ij[i][j] = 0;
			Cm_ij[i][j] = 0;
		}
	}
	index = 1;
	for (i = 0; i < imax; i++) {
		if (i == index * imax / sqrt(imax)) {
			index++;
		}
		if (i <= index * imax / sqrt(imax)) {
			X_Coordinate[i] = index;
		}
		Y_Coordinate[i] = i + 1 - (index - 1) * imax / sqrt(imax);


	}
	/*for (i = 0; i < imax; i++) {
		cout << "Coordinates[" << i << "]=(" << X_Coordinate[i] << "," << Y_Coordinate[i] << ")" << endl;
	}*/

	for (i = 1; i <= imax; i++) {
		for (j = 1; j <= jmax; j++) {
			Distance_ij[i - 1][j - 1] = abs(X_Coordinate[i - 1] - X_Coordinate[j - 1]) + abs(Y_Coordinate[i - 1] - Y_Coordinate[j - 1]);
		}
	}
	/*for (i = 1; i <= imax; i++) {
		for (j = 1; j <= jmax; j++) {
			cout << "Distance_ij[" << i << "][" << j << "]=" << Distance_ij[i - 1][j - 1] << endl;
		}
	}*/

	/*std::ostringstream os;
	os << "C:\\Data_Ambulance\\S1_dataset\\" << imax << "nodesDataset\\1-testData.txt";
	std::string FileName = os.str();
	std::ifstream fsAmbulanceData;
	fsAmbulanceData.open(FileName.c_str(), std::ios::out);

	j = 0;
	while (j < 5 * jmax && read_file != "travelCostPrimaryAssignment") {
		fsAmbulanceData >> read_file;
		j++;
	}

	for (i = 0; i < imax; i++) {
		for (j = 0; j < jmax; j++) {
			fsAmbulanceData >> Distance_ij[i][j];
		}
	}
	fsAmbulanceData.close();*/

	for (i = 0; i < imax; i++) {
		for (j = 0; j < jmax; j++) {
			if (Distance_ij[i][j] <= v_standard) {
				Cv_ij[i][j] = 1;
			}
			if (Distance_ij[i][j] <= m_standard) {
				Cm_ij[i][j] = 1;
			}
		}
	}
	Budget = sqrt(imax);
	//cout << "Budget=" << Budget << endl;

	std::random_device rd;

	//
	// Engines 
	//
	std::mt19937 generator(rd());
	//std::knuth_b e2(rd());
	//std::default_random_engine e2(rd()) ;

	//
	// Distribtuions
	//
	std::uniform_int_distribution<> dist(1, sqrt(imax));
	generator.seed(imax * Example);
	for (i = 0; i < imax; i++) {
		Importance_i[i] = dist(generator);
	}

	for (i = 0; i < imax; i++) {
		max_Cij_Dij = 0;
		for (j = 0; j < jmax; j++) {
			if ((1 - Cv_ij[i][j]) * Distance_ij[i][j] > max_Cij_Dij) {
				max_Cij_Dij = (1 - Cv_ij[i][j]) * Distance_ij[i][j];
			}
		}
		product_I_Cij_Dij = product_I_Cij_Dij + Importance_i[i] * max_Cij_Dij;
	}
	Weight = 1 / product_I_Cij_Dij;
	for (j = 0; j < jmax; j++) {
		X_vjValue[j] = 0;
		X_mjValue[j] = 0;
		OptimalX_vjValue[j] = 0;
		OptimalX_mjValue[j] = 0;
	}
	for (i = 0; i < imax; i++) {
		for (j = 0; j < jmax; j++) {
			Y_vijValue[i][j] = 0;
			Y_mijValue[i][j] = 0;
			Beta_ijValue[i][j] = 0;
			Gamma_ijValue[i][j] = 0;
			OptimalY_vijValue[i][j] = 0;
			OptimalY_mijValue[i][j] = 0;
			OptimalBeta_ijValue[i][j] = 0;
			OptimalGamma_ijValue[i][j] = 0;
		}
		Lamda1_iValue[i] = 0;
		Lamda2_iValue[i] = 0;
		OptimalLamda1_iValue[i] = 0;
		OptimalLamda2_iValue[i] = 0;
	}
	for (i = 0; i < imax; i++) {
		status_dual[i] = 0;
	}

	// End of DATA///////////////////////////
	return 0;
}
int do_master(IloEnv env, IloModel modelMaster, IloNumVarArray X_vj, IloNumVarArray X_mj, IloNumVarMatrix2x2 Y_vij, IloNumVarMatrix2x2 Y_mij, IloNumVarArray AllVars, IloRangeArray Con_Master_1n, IloRangeArray Con_Master_2n, IloRangeArray Con_Master_3i, IloRangeMatrix2x2 Con_Master_4ij, IloRangeMatrix2x2 Con_Master_5ij, IloRangeArray Con_Master_6i) {
	char CharMasterVar[60];
	char CharMasterCon[60];
	double LBMasterCon = 0;
	double UBMasterCon = 0;
	NoOfMasterVars = 0;
	NoOfMasterCons = 0;
	//------------------------------------------------------------------------------
	//---------------------------------- MASTER ------------------------------------
	//------------------------------------------------------------------------------
	//----------------------------- Master Variable --------------------------------
	//-------------- Decision Variable X_vj ---------------------------------------
	for (j = 0; j < jmax; j++) {
		sprintf(CharMasterVar, "X_vj(j%d)", j);
		IloNumVar X_v(env, 0, 1, ILOINT, CharMasterVar);
		NoOfMasterVars++;
		X_vj.add(X_v);
	}
	//-------------- Decision Variable X_mj ---------------------------------------
	for (j = 0; j < jmax; j++) {
		sprintf(CharMasterVar, "X_mj(j%d)", j);
		IloNumVar X_m(env, 0, 1, ILOINT, CharMasterVar);
		NoOfMasterVars++;
		X_mj.add(X_m);
	}

	//-------------- Decision Variable Y_vij ---------------------------------------
	for (i = 0; i < imax; i++) {
		IloNumVarArray Y_vj(env, 0);
		for (j = 0; j < jmax; j++) {
			sprintf(CharMasterVar, "Y_vij(i%d,j%d)", i, j);
			IloNumVar Y_v(env, 0, 1, ILOINT, CharMasterVar);
			NoOfMasterVars++;
			Y_vj.add(Y_v);
		}
		Y_vij.add(Y_vj);
	}

	//-------------- Decision Variable Y_mij ---------------------------------------
	for (i = 0; i < imax; i++) {
		IloNumVarArray Y_mj(env, 0);
		for (j = 0; j < jmax; j++) {
			sprintf(CharMasterVar, "Y_mij(i%d,j%d)", i, j);
			IloNumVar Y_m(env, 0, 1, ILOINT, CharMasterVar);
			NoOfMasterVars++;
			Y_mj.add(Y_m);
		}
		Y_mij.add(Y_mj);
	}




	////--------------------------- Decision Variable Z ---------------------------
	//for (n = 0; n < 1; n++) {
	//	sprintf(CharMasterVar, "Zn(n%d)", n);
	//	IloNumVar Z(env, -IloInfinity, IloInfinity, ILOFLOAT, CharMasterVar);
	//	Zn.add(Z);
	//}

	//-----------------------------Finish of Master Variables --------------------------------

	//-----------------------------------------------------------------------------
	//-------------------------Start of Master Constraints-----------------------------------------
	//------------------------------------------------------------------------------
	//------------------------------------------------------------------------------
	//-------------------------- Budget Constraint -------------------------
	for (n = 0; n < nmax; n++) {
		IloExpr expr(env, 0);
		for (j = 0; j < jmax; j++) {
			expr += P_v * X_vj[j] + P_m * X_mj[j];
		}
		sprintf(CharMasterCon, "Con_Master_1(n%d)", n);
		LBMasterCon = -IloInfinity, UBMasterCon = Budget;
		IloRange Con_Master_1(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
		NoOfMasterCons++;
		modelMaster.add(Con_Master_1);
		Con_Master_1n.add(Con_Master_1);
		expr.end();
	}

	//-------------------------- At least one van-based Constraint -------------------------
	for (n = 0; n < nmax; n++) {
		IloExpr expr(env, 0);
		for (j = 0; j < jmax; j++) {
			expr += X_vj[j];
		}
		sprintf(CharMasterCon, "Con_Master_2(n%d)", n);
		LBMasterCon = 1, UBMasterCon = IloInfinity;
		IloRange Con_Master_2(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
		NoOfMasterCons++;
		modelMaster.add(Con_Master_2);
		Con_Master_2n.add(Con_Master_2);
		expr.end();
	}


	//-------------------------- Every location assigned to exactly one van-based ambulance -------------------------
	for (i = 0; i < imax; i++) {
		IloExpr expr(env, 0);
		for (j = 0; j < jmax; j++) {
			expr += Y_vij[i][j];
		}
		sprintf(CharMasterCon, "Con_Master_3(i%d)", i);
		LBMasterCon = 1, UBMasterCon = 1;
		IloRange Con_Master_3(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
		NoOfMasterCons++;
		modelMaster.add(Con_Master_3);
		Con_Master_3i.add(Con_Master_3);
		expr.end();
	}

	//-------------------------- No assignment if station is not created (van-based ambulance) -------------------------
	for (i = 0; i < imax; i++) {
		IloRangeArray Con_Master_4j(env, 0);
		for (j = 0; j < jmax; j++) {
			IloExpr expr(env, 0);
			expr += Y_vij[i][j] - X_vj[j];
			sprintf(CharMasterCon, "Con_Master_4(i%d,j%d)", i, j);
			LBMasterCon = -IloInfinity, UBMasterCon = 0;
			IloRange Con_Master_4(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
			NoOfMasterCons++;
			modelMaster.add(Con_Master_4);
			Con_Master_4j.add(Con_Master_4);
			expr.end();
		}
		Con_Master_4ij.add(Con_Master_4j);
	}

	//-------------------------- No assignment if station is not created (motorcycle-based ambulance) -------------------------
	for (i = 0; i < imax; i++) {
		IloRangeArray Con_Master_5j(env, 0);
		for (j = 0; j < jmax; j++) {
			IloExpr expr(env, 0);
			expr += Y_mij[i][j] - X_mj[j];
			sprintf(CharMasterCon, "Con_Master_5(i%d,j%d)", i, j);
			LBMasterCon = -IloInfinity, UBMasterCon = 0;
			IloRange Con_Master_5(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
			NoOfMasterCons++;
			modelMaster.add(Con_Master_5);
			Con_Master_5j.add(Con_Master_5);
			expr.end();
		}
		Con_Master_5ij.add(Con_Master_5j);
	}


	//-------------------------- Every location assigned to exactly one van-based ambulance -------------------------
	for (i = 0; i < imax; i++) {
		IloExpr expr(env, 0);
		for (j = 0; j < jmax; j++) {
			expr += Cv_ij[i][j] * Y_vij[i][j];
		}
		for (j = 0; j < jmax; j++) {
			expr += Cm_ij[i][j] * Y_mij[i][j];
		}
		sprintf(CharMasterCon, "Con_Master_6(i%d)", i);
		LBMasterCon = 1, UBMasterCon = 1;
		IloRange Con_Master_6(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
		NoOfMasterCons++;
		modelMaster.add(Con_Master_6);
		Con_Master_6i.add(Con_Master_6);
		expr.end();
	}



	//-----------------------------------------------------------------------------
	//-------------------------Finish of Master Constraints-----------------------------------------


	//------------------------------------------------------------------------------
	//------------------------------------------------------------------------------
	//-----------------------Objective Function of Master Problem--------------------------
	//------------------------------------------------------------------------------
	IloExpr expr1(env);


	for (i = 0; i < imax; i++) {
		for (j = 0; j < jmax; j++) {
			expr1 += (Importance_i[i] * Cv_ij[i][j] * Y_vij[i][j]) - Weight * (Importance_i[i] * (1 - Cv_ij[i][j]) * Distance_ij[i][j] * Y_vij[i][j]);
		}
	}

	/*for (n = 0; n < 1; n++) {
	expr1 += Zn[n];
	}*/

	modelMaster.add(IloMaximize(env, expr1));
	expr1.end();

	return 0;
}
int Solve_Master(IloEnv env, IloModel modelMaster_ptr, IloNumVarArray X_vj, IloNumVarArray X_mj, IloNumVarMatrix2x2 Y_vij, IloNumVarMatrix2x2 Y_mij, IloCplex cplexMaster_ptr, bool* InfeasibleMaster = false) {
	OptimalOriginalObjFunction = 0;
	cplexMaster_ptr.extract(modelMaster_ptr);
	//--------------SOLVE MASTER PROBLEM----------------	
	try {
		cplexMaster_ptr.exportModel("CurrentMaster.lp");
		cplexMaster_ptr.setOut(env.getNullStream());
		cplexMaster_ptr.setParam(IloCplex::EpGap, epsilon);
		cplexMaster_ptr.setParam(IloCplex::TiLim, MaxTimeInSeconds);
		cplexMaster_ptr.solve();

		if (!cplexMaster_ptr.solve()) {
			env.error() << "Failed to optimize Master LP" << endl;
			env.out() << "------------------------------" << endl;
			*InfeasibleMaster = true;
			return 0;
		}
		int status_master = 0;

		env.out() << "Solution status Master1 = " << cplexMaster_ptr.getStatus() << endl;
		env.out() << "Solution value Master1= " << cplexMaster_ptr.getObjValue() << endl;
		status_master = cplexMaster_ptr.getStatus();
		Gap = cplexMaster_ptr.getMIPRelativeGap();
		OptimalOriginalObjFunction = cplexMaster_ptr.getObjValue();

		//--------LOWER BOUND------------
		/*if (status_master == 2) {
		UpperBound = cplexMaster_ptr.getObjValue();
		}*/
		for (j = 0; j < jmax; j++) {
			OptimalX_vjValue[j] = cplexMaster_ptr.getValue(X_vj[j]);
			/*if (X_vjValue[j] > 0) {
			cout << "X_vjValue[" << j << "]=" << X_vjValue[j] << endl;
			}*/
			OptimalX_mjValue[j] = cplexMaster_ptr.getValue(X_mj[j]);
			/*if (X_mjValue[j] > 0) {
			cout << "X_mjValue[" << j << "]=" << X_mjValue[j] << endl;
			}*/
		}
		for (i = 0; i < imax; i++) {
			for (j = 0; j < jmax; j++) {
				OptimalY_vijValue[i][j] = cplexMaster_ptr.getValue(Y_vij[i][j]);
				/*if (X_vjValue[j] > 0) {
				cout << "X_vjValue[" << j << "]=" << X_vjValue[j] << endl;
				}*/
				OptimalY_mijValue[i][j] = cplexMaster_ptr.getValue(Y_mij[i][j]);
				/*if (X_mjValue[j] > 0) {
				cout << "X_mjValue[" << j << "]=" << X_mjValue[j] << endl;
				}*/
			}
		}

		/*for (n = 0; n < 1; n++) {
		ThetaValue = cplexMaster_ptr.getValue(Zn[n]);
		}*/
		/**DTransposeY_ptr = 0;*/

		/*dTy.push_back(*DTransposeY_ptr);
		zCurrent.push_back(ThetaValue);

		OptimalThetaValue = ThetaValue;*/

	}
	catch (IloException& e) {
		cerr << "concert exception caught Master:" << e << endl;
	}
	catch (...) {
		cerr << "Unknown exception caught Master " << endl;
	}
	return 0;
}
int PrintOptimalSolution() {
	int TotalVansUsed = 0;
	int TotalMotorcyclesUsed = 0;
	for (j = 0; j < jmax; j++) {
		if (OptimalX_vjValue[j] >= 0.01) {
			TotalVansUsed++;
		}
		if (OptimalX_mjValue[j] >= 0.01) {
			TotalMotorcyclesUsed++;
		}
	}

	std::ostringstream os;
	os << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\CPLEX\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\CPLEX - OptimalSolution.txt";
	std::string FileName = os.str();

	std::ofstream fsOptimalSolution;
	fsOptimalSolution.open(FileName.c_str(), std::ios::out);
	fsOptimalSolution << "TotalSolutionTime= " << duration << " seconds " << std::endl;
	//fsOptimalSolution << "TotalIterations= " << loop << std::endl;
	fsOptimalSolution << "OptimalityGap= " << Gap << std::endl;
	fsOptimalSolution << "OptimalObjFunction= " << OptimalOriginalObjFunction << std::endl;
	fsOptimalSolution << "TotalVansUsed= " << TotalVansUsed << std::endl;
	fsOptimalSolution << "TotalMotorcyclesUsed= " << TotalMotorcyclesUsed << std::endl;
	/*fsOptimalSolution << "OptimalMasterObjFunction= " << OptimalMasterObjFunction << std::endl;
	fsOptimalSolution << "OptimalPrimalSlaveObjFunction= " << OptimalPrimalSlaveObjFunction << std::endl;
	fsOptimalSolution << "OptimalDualSlaveObjFunction= " << OptimalDualSlaveObjFunction << std::endl;*/
	fsOptimalSolution << "----------------------------------" << std::endl;
	/*if (OptimalThetaValue > 0.01) {
	fsOptimalSolution << "OptimalThetaValue= " << OptimalThetaValue << std::endl;
	}*/
	/*fsOptimalSolution << "----------------------------------" << std::endl;
	fsOptimalSolution << "TotalNumberOfFeasibilityCuts= " << BDFeasCuts << std::endl;
	fsOptimalSolution << "TotalNumberOfOptimalityCuts= " << BDOptCuts << std::endl;
	fsOptimalSolution << "TotalNumberOfMasterVariables= " << NoOfMasterVars << std::endl;
	fsOptimalSolution << "TotalNumberOfPrimalSlaveVariables= " << NoOfPrimalSlaveVars << std::endl;
	fsOptimalSolution << "TotalNumberOfMasterConstraints= " << NoOfMasterCons << std::endl;
	fsOptimalSolution << "TotalNumberOfPrimalSlaveConstraints= " << NoOfPrimalSlaveCons << std::endl;
	fsOptimalSolution << "----------------------------------" << std::endl;
	*/
	for (j = 0; j < jmax; j++) {
		if (OptimalX_vjValue[j] >= 0.01) {
			fsOptimalSolution << "OptimalX_vjValue" << "[" << j << "]" << "=" << OptimalX_vjValue[j] << std::endl;
		}
	}
	fsOptimalSolution << "----------------------------------" << std::endl;
	for (j = 0; j < jmax; j++) {
		if (OptimalX_mjValue[j] >= 0.01) {
			fsOptimalSolution << "OptimalX_mjValue" << "[" << j << "]" << "=" << OptimalX_mjValue[j] << std::endl;
		}
	}
	fsOptimalSolution << "----------------------------------" << std::endl;
	for (i = 0; i < imax; i++) {
		for (j = 0; j < jmax; j++) {
			if (OptimalY_vijValue[i][j] >= 0.01) {
				fsOptimalSolution << "OptimalY_vijValue" << "[" << i << "][" << j << "]=" << OptimalY_vijValue[i][j] << std::endl;
			}
		}
	}
	fsOptimalSolution << "----------------------------------" << std::endl;
	for (i = 0; i < imax; i++) {
		for (j = 0; j < jmax; j++) {
			if (OptimalY_mijValue[i][j] >= 0.01) {
				fsOptimalSolution << "OptimalY_mijValue" << "[" << i << "][" << j << "]=" << OptimalY_mijValue[i][j] << std::endl;
			}
		}
	}
	/*fsOptimalSolution << "----------------------------------" << std::endl;
	for (i = 0; i < imax; i++) {
	if (OptimalLamda1_iValue[i] >= 0.01) {
	fsOptimalSolution << "OptimalLamda1_iValue" << "[" << i << "]" << "=" << OptimalLamda1_iValue[i] << std::endl;
	}
	}
	fsOptimalSolution << "----------------------------------" << std::endl;
	for (i = 0; i < imax; i++) {
	if (OptimalLamda2_iValue[i] >= 0.01) {
	fsOptimalSolution << "OptimalLamda2_iValue" << "[" << i << "]" << "=" << OptimalLamda2_iValue[i] << std::endl;
	}
	}
	fsOptimalSolution << "----------------------------------" << std::endl;
	for (i = 0; i < imax; i++) {
	for (j = 0; j < jmax; j++) {
	if (OptimalBeta_ijValue[i][j] >= 0.01) {
	fsOptimalSolution << "OptimalBeta_ijValue" << "[" << i << "][" << j << "]=" << OptimalBeta_ijValue[i][j] << std::endl;
	}
	}
	}
	fsOptimalSolution << "----------------------------------" << std::endl;
	for (i = 0; i < imax; i++) {
	for (j = 0; j < jmax; j++) {
	if (OptimalGamma_ijValue[i][j] >= 0.01) {
	fsOptimalSolution << "OptimalGamma_ijValue" << "[" << i << "][" << j << "]=" << OptimalGamma_ijValue[i][j] << std::endl;
	}
	}
	}*/
	fsOptimalSolution.close();


	/*std::ostringstream LowerBound;
	LowerBound << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\CPLEX\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\CPLEX - LowerBound.txt";
	std::string FileNameLB = LowerBound.str();
	std::ofstream fsLowerBound;
	fsLowerBound.open(FileNameLB.c_str(), std::ios::out);
	for (i = 0; i < LowerBoundArray.size(); i++) {
	fsLowerBound << LowerBoundArray.at(i) << std::endl;
	}
	fsLowerBound.close();

	std::ostringstream UpperBound;
	UpperBound << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\CPLEX\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\CPLEX - UpperBound.txt";
	std::string FileNameUB = UpperBound.str();
	std::ofstream fsUpperBound;
	fsUpperBound.open(FileNameUB.c_str(), std::ios::out);
	for (i = 0; i < UpperBoundArray.size(); i++) {
	fsUpperBound << UpperBoundArray.at(i) << std::endl;
	}
	fsUpperBound.close();

	std::ostringstream LowerBoundGlobal;
	LowerBoundGlobal << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\CPLEX\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\CPLEX - LowerBoundGlobal.txt";
	std::string FileNameUBG = LowerBoundGlobal.str();
	std::ofstream fsLowerBoundGlobal;
	fsLowerBoundGlobal.open(FileNameUBG.c_str(), std::ios::out);
	for (i = 0; i < LowerBoundGlobalArray.size(); i++) {
	fsLowerBoundGlobal << LowerBoundGlobalArray.at(i) << std::endl;
	}
	fsLowerBoundGlobal.close();


	std::ostringstream dTransY;
	dTransY << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\CPLEX\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\CPLEX - DTrasnposeY.txt";
	std::string FileNameDTY = dTransY.str();
	std::ofstream fsdTransY;
	fsdTransY.open(FileNameDTY.c_str(), std::ios::out);
	for (i = 0; i < dTy.size(); i++) {
	fsdTransY << dTy.at(i) << std::endl;
	}
	fsdTransY.close();

	std::ostringstream cTransX;
	cTransX << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\CPLEX\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\CPLEX - CTrasnposeX.txt";
	std::string FileNameCTX = cTransX.str();
	std::ofstream fscTransX;
	fscTransX.open(FileNameCTX.c_str(), std::ios::out);
	for (i = 0; i < cTx.size(); i++) {
	fscTransX << cTx.at(i) << std::endl;
	}
	fscTransX.close();

	std::ostringstream bTransU;
	bTransU << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\CPLEX\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\CPLEX - BTrasnposeU.txt";
	std::string FileNameBTU = bTransU.str();
	std::ofstream fsbTransU;
	fsbTransU.open(FileNameBTU.c_str(), std::ios::out);
	for (i = 0; i < bTu.size(); i++) {
	fsbTransU << bTu.at(i) << std::endl;
	}
	fsbTransU.close();

	std::ostringstream CurrentTheta;
	CurrentTheta << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\CPLEX\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\CPLEX - CurrentTheta.txt";
	std::string FileNameCurrentTheta = CurrentTheta.str();
	std::ofstream fsCurrentTheta;
	fsCurrentTheta.open(FileNameCurrentTheta.c_str(), std::ios::out);
	for (i = 0; i < zCurrent.size(); i++) {
	fsCurrentTheta << zCurrent.at(i) << std::endl;
	}
	fsCurrentTheta.close();

	std::ostringstream BestPrimalSlaveObj;
	BestPrimalSlaveObj << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\CPLEX\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\CPLEX - BestPrimalSlaveObjSoFar.txt";
	std::string FileNameBPSO = BestPrimalSlaveObj.str();
	std::ofstream fsBestPrimalSlaveObj;
	fsBestPrimalSlaveObj.open(FileNameBPSO.c_str(), std::ios::out);
	for (i = 0; i < BestPrimalSlaveObjSoFar.size(); i++) {
	fsBestPrimalSlaveObj << BestPrimalSlaveObjSoFar.at(i) << std::endl;
	}
	fsBestPrimalSlaveObj.close();

	std::ostringstream BestDualSlaveObj;
	BestDualSlaveObj << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\CPLEX\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\CPLEX - BestDualSlaveObjSoFar.txt";
	std::string FileNameBDSO = BestDualSlaveObj.str();
	std::ofstream fsBestDualSlaveObj;
	fsBestDualSlaveObj.open(FileNameBDSO.c_str(), std::ios::out);
	for (i = 0; i < BestDualSlaveObjSoFar.size(); i++) {
	fsBestDualSlaveObj << BestDualSlaveObjSoFar.at(i) << std::endl;
	}
	fsBestDualSlaveObj.close();



	std::ostringstream TimePath;
	TimePath << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\CPLEX\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\CPLEX - Time.txt";
	std::string FileNameTime = TimePath.str();
	std::ofstream fsTime;
	fsTime.open(FileNameTime.c_str(), std::ios::out);
	for (i = 0; i < Time.size(); i++) {
	fsTime << Time.at(i) << std::endl;
	}
	fsTime.close();*/

	std::ostringstream DataDistance;
	DataDistance << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\CPLEX\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\CPLEX - Distance.txt";
	std::string FileNameDataDistance = DataDistance.str();
	std::ofstream fsDataDistance;
	fsDataDistance.open(FileNameDataDistance.c_str(), std::ios::out);
	for (i = 0; i < imax; i++) {
		for (j = 0; j < jmax; j++) {
			fsDataDistance << Distance_ij[i][j] << "\t";
		}
		fsDataDistance << std::endl;
	}
	fsDataDistance.close();

	std::ostringstream Data;
	Data << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\CPLEX\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\CPLEX - Data.txt";
	std::string FileNameData = Data.str();
	std::ofstream fsData;
	fsData.open(FileNameData.c_str(), std::ios::out);
	fsData << "Importance[i]" << std::endl;
	for (i = 0; i < imax; i++) {
		fsData << Importance_i[i] << "\t";
	}
	fsData << std::endl;
	fsData << "P_m" << std::endl;
	fsData << P_m << std::endl;
	fsData << "P_v" << std::endl;
	fsData << P_v << std::endl;
	fsData << "Weight" << std::endl;
	fsData << Weight << std::endl;
	fsData << "Budget" << std::endl;
	fsData << Budget << std::endl;

	fsData.close();







	//std::ostringstream SlackVals;
	//SlackVals << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\CPLEX\\CPLEX - SlackValuesBendersCuts.txt";
	//std::string FileNameSlack = SlackVals.str();
	//std::ofstream fsSlack;
	//fsSlack.open(FileNameSlack.c_str(), std::ios::out);
	//i = 0;
	//j = 0;
	//int k = 0;
	//int z = 0;
	//while (j<BDFeasCuts + BDOptCuts) {
	//	z = 0;
	//	k += NoOfCutsInEachIteration.at(j);
	//	while (i<SlackValuesOfBendersCuts.size() && z<k) {
	//		fsSlack << SlackValuesOfBendersCuts.at(i) << "\t";
	//		z++;
	//		i++;
	//	}
	//	fsSlack << std::endl;
	//	j++;
	//}
	//fsSlack.close();

	//cout << "Max size of vector SlackValuesOfMainMasterCons=" << SlackValuesOfMainMasterCons.max_size() << endl;
	//cout << "Current size of vector SlackValuesOfMainMasterCons=" << SlackValuesOfMainMasterCons.size() << endl;
	/*std::ostringstream SlackValsMasterCons;
	SlackValsMasterCons << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\CPLEX\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\CPLEX - SlackValuesMainMasterCons.txt";
	std::string FileNameSlackMaster = SlackValsMasterCons.str();
	std::ofstream fsSlackMasterCons;
	fsSlackMasterCons.open(FileNameSlackMaster.c_str(), std::ios::out);
	for (i = 0; i < SlackValuesOfMainMasterCons.size(); i++) {
	fsSlackMasterCons << SlackValuesOfMainMasterCons.at(i) << "\t";
	if ((i + 1) % NoOfMasterCons == 0) {
	fsSlackMasterCons << std::endl;
	}
	}
	fsSlackMasterCons.close();
	*/
	return 0;
}
int main(int argc, char** argv)
{
	int  stop, status;
	for (Case = 1; Case <= 1; Case++) {
		for (Example = 1; Example <= 10; Example++) {
			cout << "Case= " << Case << endl;
			cout << "Example= " << Example << endl;
			//--------Declare the environment of CPLEX----------------
			IloEnv env;

			Gap = 1;
			try {
				//--------Construct models----------------
				IloModel modelDualSlave(env);
				IloModel modelMaster(env);
				//------Declare Decision Variables----------
				IloNumVarArray X_vj(env, 0);
				IloNumVarArray X_mj(env, 0);
				IloNumVarMatrix2x2 Y_vij(env, 0);
				IloNumVarMatrix2x2 Y_mij(env, 0);

				IloNumVarArray AllVars(env, 0);

				//--------Declare Master constraints-------------
				IloRangeArray Con_Master_1n(env, 0);
				IloRangeArray Con_Master_2n(env, 0);
				IloRangeArray Con_Master_3i(env, 0);
				IloRangeMatrix2x2 Con_Master_4ij(env, 0);
				IloRangeMatrix2x2 Con_Master_5ij(env, 0);
				IloRangeArray Con_Master_6i(env, 0);

				//--------Declare Array of Benders Cuts Added in Master Problem-------------
				IloRangeArray BendersCuts(env, 0);

				//--------Declare dual variables of each constraint----------------
				IloNumArray ExtremeRayArray(env, 0);
				IloNumArray SlackValues(env, 0);
				IloNum SlackValuesMasterCons = 0;



				start = clock();

				status = load_data();
				if (status != 0) {
					Found_Error("load_data");
					return -1;
				}

				status = do_master(env, modelMaster, X_vj, X_mj, Y_vij, Y_mij, AllVars, Con_Master_1n, Con_Master_2n, Con_Master_3i, Con_Master_4ij, Con_Master_5ij, Con_Master_6i);
				if (status != 0) {
					Found_Error("do_master");
					return -1;
				}
				bool InfeasibleMaster = false;
				IloCplex cplexMaster_ptr(env);
				cplexMaster_ptr.extract(modelMaster);
				cplexMaster_ptr.exportModel("modelMaster1.lp");
				status = Solve_Master(env, modelMaster, X_vj, X_mj, Y_vij, Y_mij, cplexMaster_ptr, &InfeasibleMaster);
				if (status != 0) {
					Found_Error("Solve_Master");
					return -1;
				}
				/*
				status = do_dual_slave();
				if (status != 0) {
				Found_Error("do_dual_slave");
				return -1;
				}
				*/

				/*status = BendersIteration(modelMaster, modelDualSlave);
				if (status != 0) {
				Found_Error("BendersIteration");
				return -1;
				}*/
				stop = clock();
				duration = (long double)(stop - start) / CLOCKS_PER_SEC;

				status = PrintOptimalSolution();
				if (status != 0) {
					Found_Error("PrintOptimalSolution");
					return -1;
				}
			}
			catch (IloException& e) {
				cout << "Error : " << e << endl;
			}

			env.end();

			printf("Code terminated successfully \n");
			printf("Execution time = %Lf seconds\n", duration);
		}
	}
	return 0;

} //End main