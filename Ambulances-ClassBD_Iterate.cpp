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
const int imax = 900;
const int jmax = 900;
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
double MasterGap = 0.001;
int loop;
int MaxIterations = 5000;
int MaxDuration = 7200;//seconds
int MasterMaxDuration;//seconds
double UpperBound;
double LowerBound;
double LowerBoundGlobal;
double Gap;
double fraction = 0.90;
long double Duration, DurationMaster, DurationSlave;  // tracks time
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
	BDFeasCuts = 0, BDOptCuts = 0, CutsPerIteration = 0, NoOfMasterVars = 0, NoOfPrimalSlaveVars = 0, NoOfDualSlaveVars = 0, NoOfMasterCons = 0, NoOfPrimalSlaveCons = 0, NoOfDualSlaveCons = 0;
	ThetaValue = 0;
	OptimalThetaValue = 0;

	OriginalObjFunction = 0;
	MasterObjFunction = 0;
	PrimalSlaveObjFunction = 0;
	DualSlaveObjFunction = 0;

	OptimalOriginalObjFunction = 0;
	OptimalMasterObjFunction = 0;
	OptimalPrimalSlaveObjFunction = 0;
	OptimalDualSlaveObjFunction = 0;

	// End of DATA///////////////////////////
	return 0;
}
int do_master(IloEnv env, IloModel modelMaster, IloNumVarArray X_vj, IloNumVarArray X_mj, IloNumVarArray Zn, IloNumVarArray AllVars, IloRangeArray Con_Master_1n, IloRangeArray Con_Master_2n, IloRangeArray Con_Master_3i) {
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

	//--------------------------- Decision Variable Z ---------------------------
	for (n = 0; n < 1; n++) {
		sprintf(CharMasterVar, "Zn(n%d)", n);
		IloNumVar Z(env, -IloInfinity, Big_M, ILOFLOAT, CharMasterVar);
		Zn.add(Z);
	}

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
	//-------------------------- At least one van-based or motor-based for every node Constraint -------------------------
	for (i = 0; i < imax; i++) {
		/*bool CloseNodeAdded = false;
		FeasCutForNodeAdded_i[i] = false;*/
		/*for (j = 0; j < jmax; j++) {
			if ((Distance_ij[i][j] < v_standard || Distance_ij[j][i] < v_standard) && FeasCutForNodeAdded_i[j] == true) {
				CloseNodeAdded = true;
			}
		}
		if (CloseNodeAdded == false) {*/
		IloExpr expr(env, 0);
		for (j = 0; j < jmax; j++) {
			if (Cv_ij[i][j] == 1) {
				expr += X_vj[j];
			}
			if (Cm_ij[i][j] == 1) {
				expr += X_mj[j];
			}
		}
		sprintf(CharMasterCon, "Con_Master_3(i%d)", i);
		LBMasterCon = 1, UBMasterCon = IloInfinity;
		IloRange Con_Master_3(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
		NoOfMasterCons++;
		modelMaster.add(Con_Master_3);
		Con_Master_3i.add(Con_Master_3);
		expr.end();
		//FeasCutForNodeAdded_i[i] = true;
	//}
	}


	//-----------------------------------------------------------------------------
	//-------------------------Finish of Master Constraints-----------------------------------------


	//------------------------------------------------------------------------------
	//------------------------------------------------------------------------------
	//-----------------------Objective Function of Master Problem--------------------------
	//------------------------------------------------------------------------------
	IloExpr expr1(env);

	for (n = 0; n < 1; n++) {
		expr1 += Zn[n];
	}

	modelMaster.add(IloMaximize(env, expr1));
	expr1.end();

	return 0;
}
int do_dual_slave(IloEnv env, IloModel modelDualSlave, IloNumVarArray Lamda1_i, IloNumVarArray Lamda2_i, IloNumVarMatrix2x2 Beta_ij, IloNumVarMatrix2x2 Gamma_ij, IloNumVarArray AllVars, IloRangeMatrix2x2 Con_Slave_1ij, IloRangeMatrix2x2 Con_Slave_2ij) {
	char CharSlaveVar[60];
	char CharSlaveCon[60];
	double LBSlaveCon = 0;
	double UBSlaveCon = 0;
	NoOfDualSlaveVars = 0;
	NoOfDualSlaveCons = 0;
	//--------------------------- DUAL SLAVE PROBLEM OF LOCATION i (DSPi) ----------------------------------
	//------------------------------------------------------------------------------
	//--------------------------- Slave Dual Variables ---------------------------
	//--------------------------- Decision Variable Lamda1_i ---------------------------
	for (i = 0; i < imax; i++) {
		sprintf(CharSlaveVar, "Lamda1_i(i%d)", i);
		IloNumVar Lamda1(env, -IloInfinity, IloInfinity, ILOFLOAT, CharSlaveVar);
		NoOfDualSlaveVars++;
		Lamda1_i.add(Lamda1);
		AllVars.add(Lamda1);
	}

	//--------------------------- Decision Variable Lamda2_i ---------------------------
	for (i = 0; i < imax; i++) {
		sprintf(CharSlaveVar, "Lamda2_i(i%d)", i);
		IloNumVar Lamda2(env, -IloInfinity, IloInfinity, ILOFLOAT, CharSlaveVar);
		NoOfDualSlaveVars++;
		Lamda2_i.add(Lamda2);
		AllVars.add(Lamda2);
	}

	//--------------------------- Decision Variable Beta_ij --------------------------
	for (i = 0; i < imax; i++) {
		IloNumVarArray Beta_j(env, 0);
		for (j = 0; j < jmax; j++) {
			sprintf(CharSlaveVar, "Beta_ij(i%d,j%d)", i, j);
			IloNumVar Beta(env, 0, IloInfinity, ILOFLOAT, CharSlaveVar);
			NoOfDualSlaveVars++;
			Beta_j.add(Beta);
			AllVars.add(Beta);
		}
		Beta_ij.add(Beta_j);
	}

	//--------------------------- Decision Variable Gamma_ij --------------------------
	for (i = 0; i < imax; i++) {
		IloNumVarArray Gamma_j(env, 0);
		for (j = 0; j < jmax; j++) {
			sprintf(CharSlaveVar, "Gamma_ij(i%d,j%d)", i, j);
			IloNumVar Gamma(env, 0, IloInfinity, ILOFLOAT, CharSlaveVar);
			NoOfDualSlaveVars++;
			Gamma_j.add(Gamma);
			AllVars.add(Gamma);
		}
		Gamma_ij.add(Gamma_j);
	}
	//----------------- END OF DECISION VARIABLES ------------------
	//-----------------------------------------------------------------------------
	//------------------------- Slave Dual Constraints ------------------------
	//-----------------------------------------------------------------------------
	//------------------------------ Con_Slave_1ij ------------------------------
	for (i = 0; i < imax; i++) {
		IloRangeArray Con_Slave_1j(env, 0);
		for (j = 0; j < jmax; j++) {
			IloExpr expr(env, 0);
			expr += Lamda1_i[i] + Cv_ij[i][j] * Lamda2_i[i] + Beta_ij[i][j] - Importance_i[i] * Cv_ij[i][j] + Weight * Importance_i[i] * (1 - Cv_ij[i][j]) * Distance_ij[i][j];
			sprintf(CharSlaveCon, "Con_Slave_1ij(i%d,j%d)", i, j);
			LBSlaveCon = 0, UBSlaveCon = IloInfinity;
			IloRange Con_Slave_1(env, LBSlaveCon, expr, UBSlaveCon, CharSlaveCon);
			NoOfDualSlaveCons++;
			modelDualSlave.add(Con_Slave_1);
			Con_Slave_1j.add(Con_Slave_1);
			expr.end();
		}
		Con_Slave_1ij.add(Con_Slave_1j);
	}


	//------------------------------ Con_Slave_2ij ------------------------------
	for (i = 0; i < imax; i++) {
		IloRangeArray Con_Slave_2j(env, 0);
		for (j = 0; j < jmax; j++) {
			IloExpr expr(env, 0);
			expr += Cm_ij[i][j] * Lamda2_i[i] + Gamma_ij[i][j];
			sprintf(CharSlaveCon, "Con_Slave_2ij(i%d,j%d)", i, j);
			LBSlaveCon = 0, UBSlaveCon = IloInfinity;
			IloRange Con_Slave_2(env, LBSlaveCon, expr, UBSlaveCon, CharSlaveCon);
			NoOfDualSlaveCons++;
			modelDualSlave.add(Con_Slave_2);
			Con_Slave_2j.add(Con_Slave_2);
			expr.end();
		}
		Con_Slave_2ij.add(Con_Slave_2j);
	}
	/*IloNumArray Dual_Obj_Coefs_Lamda1(env, imax);
	l = 0;
	for (i = 0; i < imax; i++) {
	Dual_Obj_Coefs_Lamda1[l] = 1;
	cout << "Dual_Obj_Coefs[" << l << "]=" << Dual_Obj_Coefs_Lamda1[l] << endl;
	l++;
	}
	Dual_objective.setLinearCoefs(Lamda1_i, Dual_Obj_Coefs_Lamda1);
	*/



	return 0;
}

int Solve_Master(IloEnv env, IloModel modelMaster_ptr, IloCplex cplexMaster_ptr, IloNumVarArray X_vj, IloNumVarArray X_mj, IloNumVarArray Zn, double* DTransposeY_ptr, bool* InfeasibleMaster = false) {
	MasterMaxDuration = (MaxDuration - ((clock() - start) / CLOCKS_PER_SEC)) / 2;
	cplexMaster_ptr.extract(modelMaster_ptr);
	//--------------SOLVE MASTER PROBLEM----------------	
	try {
		cplexMaster_ptr.exportModel("CurrentMaster.lp");
		cplexMaster_ptr.setOut(env.getNullStream());
		cplexMaster_ptr.setParam(IloCplex::EpGap, MasterGap);
		cplexMaster_ptr.setParam(IloCplex::TiLim, MasterMaxDuration);
		cplexMaster_ptr.solve();

		if (!cplexMaster_ptr.solve()) {
			env.error() << "Failed to optimize Master." << endl;
			env.out() << "----------------------------------------------------------------" << endl;
			*InfeasibleMaster = true;
			return 0;
		}
		int status_master = 0;

		//env.out() << "Solution status Master = " << cplexMaster_ptr.getStatus() << endl;
		//env.out() << "Solution value Master= " << cplexMaster_ptr.getObjValue() << endl;
		status_master = cplexMaster_ptr.getStatus();
		//--------LOWER BOUND------------
		if (status_master == 2 || status_master == 1) {
			UpperBound = cplexMaster_ptr.getObjValue();
		}
		for (j = 0; j < jmax; j++) {
			X_vjValue[j] = cplexMaster_ptr.getValue(X_vj[j]);
			/*if (X_vjValue[j] > 0) {
				cout << "X_vjValue[" << j << "]=" << X_vjValue[j] << endl;
			}*/
			X_mjValue[j] = cplexMaster_ptr.getValue(X_mj[j]);
			/*if (X_mjValue[j] > 0) {
				cout << "X_mjValue[" << j << "]=" << X_mjValue[j] << endl;
			}*/
		}

		for (n = 0; n < 1; n++) {
			ThetaValue = cplexMaster_ptr.getValue(Zn[n]);
		}
		*DTransposeY_ptr = 0;

		dTy.push_back(*DTransposeY_ptr);
		zCurrent.push_back(ThetaValue);

		OptimalThetaValue = ThetaValue;

	}
	catch (IloException& e) {
		cerr << "concert exception caught Master:" << e << endl;
	}
	catch (...) {
		cerr << "Unknown exception caught Master " << endl;
	}
	return 0;
}
int Get_Slack_Values(IloCplex cplexMaster_ptr, IloNum SlackValuesMasterCons, IloNumArray SlackValues, IloRangeArray Con_Master_1n, IloRangeArray Con_Master_2n, IloRangeArray BendersCuts) {
	//---------------Get SLACK values of the constraints of MASTER problem----------------

	for (n = 0; n < nmax; n++) {
		SlackValuesMasterCons = cplexMaster_ptr.getSlack(Con_Master_1n[n]);
		SlackValuesOfMainMasterCons.push_back(SlackValuesMasterCons);
	}
	for (n = 0; n < nmax; n++) {
		SlackValuesMasterCons = cplexMaster_ptr.getSlack(Con_Master_2n[n]);
		SlackValuesOfMainMasterCons.push_back(SlackValuesMasterCons);
	}

	/*
	IloRangeMatrix2x2 CT3Melzt(env,0);
	IloRangeMatrix2x2 CT3C_ou_Dzt(env,0);
	IloRangeMatrix2x2 SupFzj0(env,0);
	IloRangeMatrix2x2 SupCiz0(env,0);
	IloRangeMatrix2x2 SupDkz0(env,0);
	IloRangeMatrix2x2 Con3W1it(env,0);
	IloRangeMatrix2x2 Con5W2kt(env,0);
	*/
	//	cout<<"size of SLACK Array ="<<SlackValues.getSize()<<endl;

	cplexMaster_ptr.getSlacks(SlackValues, BendersCuts);
	//	cout<<"size of SLACK Array ="<<SlackValues.getSize()<<endl;

	for (l = 0; l < SlackValues.getSize(); l++) {
		/*
		if(SlackValues[l]!=0){
		cout<<"SlackValues["<<l<<"]="<<SlackValues[l]<<endl;
		}
		*/
		SlackValuesOfBendersCuts.push_back(SlackValues[l]);
	}
	/*

	for (l=0;l<SlackValuesOfBendersCuts.size();l++){

	cout<<"SlackValuesOfBendersCuts["<<l<<"]="<<SlackValuesOfBendersCuts[l]<<endl;

	}
	*/
	return 0;
}
int UpdateDualSlaveObjective(IloEnv env, IloNumVarArray Lamda1_i_ptr, IloNumVarArray Lamda2_i_ptr, IloNumVarMatrix2x2 Beta_ij_ptr, IloNumVarMatrix2x2 Gamma_ij_ptr, IloNumArray Dual_Obj_Coefs, IloObjective Dual_objective_ptr_ptr_ptr) {
	int l = 0;
	//---------------Update the objective function of the DUAL SLAVE problem---------------- 

	//IloNumArray Dual_Obj_Coefs_Lamda1(env, imax);
	l = 0;
	for (i = 0; i < imax; i++) {
		Dual_Obj_Coefs[l] = 1;
		//cout << "Dual_Obj_Coefs[" << l << "]=" << Dual_Obj_Coefs[l] << endl;
		l++;
	}
	Dual_objective_ptr_ptr_ptr.setLinearCoefs(Lamda1_i_ptr, Dual_Obj_Coefs);

	//IloNumArray Dual_Obj_Coefs_Lamda2(env, imax);
	l = 0;
	for (i = 0; i < imax; i++) {
		Dual_Obj_Coefs[l] = 1;
		//cout << "Dual_Obj_Coefs[" << l << "]=" << Dual_Obj_Coefs[l] << endl;
		l++;
	}
	Dual_objective_ptr_ptr_ptr.setLinearCoefs(Lamda2_i_ptr, Dual_Obj_Coefs);


	for (i = 0; i < imax; i++) {
		//IloNumArray Dual_Obj_Coefs_Beta(env, imax);
		l = 0;
		for (j = 0; j < jmax; j++) {
			Dual_Obj_Coefs[l] = X_vjValue[j];
			//cout << "Dual_Obj_Coefs[" << l << "]=" << Dual_Obj_Coefs[l] << endl;
			l++;
		}
		Dual_objective_ptr_ptr_ptr.setLinearCoefs(Beta_ij_ptr[i], Dual_Obj_Coefs);
	}

	for (i = 0; i < imax; i++) {
		//IloNumArray Dual_Obj_Coefs_Gamma(env, imax);
		l = 0;
		for (j = 0; j < jmax; j++) {
			Dual_Obj_Coefs[l] = X_mjValue[j];
			//cout << "Dual_Obj_Coefs[" << l << "]=" << Dual_Obj_Coefs[l] << endl;
			l++;
		}
		Dual_objective_ptr_ptr_ptr.setLinearCoefs(Gamma_ij_ptr[i], Dual_Obj_Coefs);
	}

	return 0;
}
/*int UpdateSlaveRHS(){
//---------------Update the LB of the constraints of SLAVE problem----------------

for (z=0;z<zmax;z++){
for (t=0;t<tmax;t++){
for(i=0;i<imax;i++){
CT1Fonctionement_Cizt[i][z][t].setLB(-m*CiztValue[i][z][t]);
CT2Fonctionement_Cizt[i][z][t].setLB(CiztValue[i][z][t]);
SC2_Cizt[i][z][t].setLB(-1*CiztValue[i][z][t]);
}
for(k=0;k<kmax;k++){
CT1Fonctionement_Dkzt[k][z][t].setLB(-m*DkztValue[k][z][t]);
CT2Fonctionement_Dkzt[k][z][t].setLB(DkztValue[k][z][t]);
SD2_Dkzt[k][z][t].setLB(-1*DkztValue[k][z][t]);
}
for (j=0;j<jmax;j++){
CT1Melzjt[z][j][t].setLB(-m*FzjtValue[z][j][t]);
CT2Melzjt[z][j][t].setLB(FzjtValue[z][j][t]);
}
}
}

for(i=0;i<imax;i++){
for (z=0;z<zmax;z++){
for (t=0;t<tmax;t++){
if(t==0){
SC_Cizt[i][z][t].setLB(CiztValue[i][z][t]);
}else{
SC_Cizt[i][z][t].setLB(CiztValue[i][z][t]-CiztValue[i][z][t-1]);
}
}
}
}
for(k=0;k<kmax;k++){
for (z=0;z<zmax;z++){
for (t=0;t<tmax;t++){
if(t==0){
SD_Dkzt[k][z][t].setLB(DkztValue[k][z][t]);
}else{
SD_Dkzt[k][z][t].setLB(DkztValue[k][z][t]-DkztValue[k][z][t-1]);
}
}
}
}
return 0;
}*/
int Solve_Dual_Slave(IloEnv env, IloModel modelDualSlave_ptr, IloCplex cplexDualSlave_ptr, IloNumVarArray Lamda1_i, IloNumVarArray Lamda2_i, IloNumVarMatrix2x2 Beta_ij, IloNumVarMatrix2x2 Gamma_ij, IloObjective Dual_objective_ptr_ptr) {
	cplexDualSlave_ptr.extract(modelDualSlave_ptr);
	//-----------Solve Slave Problem--------------
	try {
		cplexDualSlave_ptr.setParam(IloCplex::PreInd, 0);
		cplexDualSlave_ptr.setParam(IloCplex::ScaInd, -1);
		cplexDualSlave_ptr.setParam(IloCplex::RootAlg, IloCplex::Primal);
		cplexDualSlave_ptr.exportModel("CurrentDualSlave.lp");
		cplexDualSlave_ptr.setOut(env.getNullStream());
		cplexDualSlave_ptr.solve();
		//env.out() << "Solution status of DUAL SLAVE problem = " << cplexDualSlave_ptr.getStatus() << endl;
		//env.out() << "Solution value of DUAL SLAVE problem = " << cplexDualSlave_ptr.getObjValue() << endl;

		for (i = 0; i < imax; i++) {
			Lamda1_iValue[i] = cplexDualSlave_ptr.getValue(Lamda1_i[i]);
			Lamda2_iValue[i] = cplexDualSlave_ptr.getValue(Lamda2_i[i]);
			/*if (Lamda2_iValue[i] > 0) {
				cout << "Lamda2_iValue[" << i << "]=" << Lamda2_iValue[i] << endl;
			}*/
			for (j = 0; j < jmax; j++) {
				Beta_ijValue[i][j] = cplexDualSlave_ptr.getValue(Beta_ij[i][j]);
				Gamma_ijValue[i][j] = cplexDualSlave_ptr.getValue(Gamma_ij[i][j]);
				/*if (Gamma_ijValue[i][j] > 0) {
					cout << "Gamma_ijValue[" << i << "][" << j << "]=" << Gamma_ijValue[i][j] << endl;
				}*/
			}
		}

	}//end of try(try of primal slave 1)

	catch (IloException& e) {
		cerr << "concert exception caught:" << e << endl;
	}
	catch (...) {
		cerr << "Unknown exception caught" << endl;
	}
	return 0;
}
int Dual_Slave_Unbounded(IloEnv env, double* DualSlaveObjFunction, double* PrimalSlaveObjFunction) {
	//env.error() << "Dual Slave Problem is UNBOUNDED" << endl;
	//env.out() << "----------------------------------------------------------------" << endl;
	//------Lower Bound Global remains the same--------
	LowerBound = -Big_M;
	LowerBoundGlobal = LowerBoundGlobal;

	*PrimalSlaveObjFunction = 0;
	*DualSlaveObjFunction = -Big_M;

	return 0;
}
int Dual_Slave_Bounded(IloEnv env, IloCplex cplexDualSlave_ptr, double* DTransposeY, double* DualSlaveObjFunction, double* PrimalSlaveObjFunction, int loop_ptr, IloRangeMatrix2x2 Con_Slave_1ij, IloRangeMatrix2x2 Con_Slave_2ij) {
	//env.error() << "Dual Slave Problem is BOUNDED" << endl;
	//env.error() << "Found a FEASIBLE solution of Slave LP" << endl;
	//env.out() << "----------------------------------------------------------------" << endl;
	*DualSlaveObjFunction = cplexDualSlave_ptr.getObjValue();
	int status = 0;
	for (i = 0; i < imax; i++) {
		for (j = 0; j < jmax; j++) {
			Y_vijValue[i][j] = cplexDualSlave_ptr.getDual(Con_Slave_1ij[i][j]);
		}
	}
	for (i = 0; i < imax; i++) {
		for (j = 0; j < jmax; j++) {
			Y_mijValue[i][j] = cplexDualSlave_ptr.getDual(Con_Slave_2ij[i][j]);
		}
	}

	*PrimalSlaveObjFunction = 0;

	for (i = 0; i < imax; i++) {
		for (j = 0; j < jmax; j++) {
			*PrimalSlaveObjFunction += Importance_i[i] * Cv_ij[i][j] * Y_vijValue[i][j];
		}
	}
	for (i = 0; i < imax; i++) {
		for (j = 0; j < jmax; j++) {
			*PrimalSlaveObjFunction -= Weight * Importance_i[i] * (1 - Cv_ij[i][j]) * Distance_ij[i][j] * Y_vijValue[i][j];
		}
	}
	LowerBound = *DTransposeY + *PrimalSlaveObjFunction;

	if (LowerBound < LowerBoundGlobal) {//-----We found a worse feasible solution---
		LowerBoundGlobal = LowerBoundGlobal;
	}
	else {//-----------We found a better feasible solution-------
		LowerBoundGlobal = LowerBound;//Update Upper Bound
		OptimalOriginalObjFunction = LowerBoundGlobal;
		OptimalMasterObjFunction = *DTransposeY + ThetaValue;
		OptimalPrimalSlaveObjFunction = *PrimalSlaveObjFunction;
		OptimalDualSlaveObjFunction = *DualSlaveObjFunction;
		for (j = 0; j < jmax; j++) {
			OptimalX_vjValue[j] = X_vjValue[j];
			OptimalX_mjValue[j] = X_mjValue[j];
		}
		for (i = 0; i < imax; i++) {
			for (j = 0; j < jmax; j++) {
				OptimalY_vijValue[i][j] = Y_vijValue[i][j];
				OptimalY_mijValue[i][j] = Y_mijValue[i][j];
				OptimalBeta_ijValue[i][j] = Beta_ijValue[i][j];
				OptimalGamma_ijValue[i][j] = Gamma_ijValue[i][j];
			}
			OptimalLamda1_iValue[i] = Lamda1_iValue[i];
			OptimalLamda2_iValue[i] = Lamda2_iValue[i];
		}

		OptimalThetaValue = ThetaValue;

	}//end of else (better feasible solution found)

	return 0;
}
int GetExtremeRayOfDSP(IloCplex cplexDualSlave_ptr, IloNumArray ExtremeRayArray, IloNumVarArray Lamda1_i, IloNumVarArray Lamda2_i, IloNumVarMatrix2x2 Beta_ij, IloNumVarMatrix2x2 Gamma_ij, IloNumVarArray AllVars) {
	//----------------Get an extreme ray of the DUAL SLAVE problem-------------
	//cout<<"size of Array ="<<FeasvalsDualRangeSumXijt.getSize()<<endl;

	//cplexSlave_ptr.dualFarkas(SumXijt[0][0],FeasvalsDualRangeSumXijt);
	//cout<<"size of Array ="<<FeasvalsDualRangeSumXijt.getSize()<<endl;
	/*
	for (l=0;l<FeasvalsDualRangeSumXijt.getSize();l++){
	if(FeasvalsDualRangeSumXijt[l]!=0){
	cout<<"FeasvalsDualRangeSumXijt["<<l<<"]="<<FeasvalsDualRangeSumXijt[l]<<endl;
	}
	}
	*/


	//IloExpr ray=cplexDualSlave_ptr.getRay();
	//System.out.println("getRay returned " + ray.toString());
	for (i = 0; i < imax; i++) {
		Lamda1_iValue[i] = 0;
		Lamda2_iValue[i] = 0;
		for (j = 0; j < jmax; j++) {
			Beta_ijValue[i][j] = 0;
			Gamma_ijValue[i][j] = 0;
		}
	}

	//cout << "size of variables =" << AllVars.getSize() << endl;
	//cout << "size of Array =" << ExtremeRayArray.getSize() << endl;
	cplexDualSlave_ptr.getRay(ExtremeRayArray, AllVars);

	//cout << "size of Array =" << ExtremeRayArray.getSize() << endl;
	//cout << "size of variables =" << AllVars.getSize() << endl;

	//IloNumExpr rayantonis;
	//cplexDualSlave_ptr.getRay(rayantonis,U1ijt[0][0]);
	for (l = 0; l < ExtremeRayArray.getSize(); l++) {
		if (ExtremeRayArray[l] != 0) {
			//cout<<"ExtremeRayArray["<<l<<"]="<<ExtremeRayArray[l]<<endl;
		}
	}

	//sprintf(Dual1,"U1ijt(i%d,j%d,t%d)",i,j,t);
	//for ( l = 0; l < ExtremeRayArray.getSize(); ++l){
	//cout << l << ", " << ExtremeRayArray[l] << " [" << U1ijt[l].getImpl() << "]"<<endl;

	//}


	for (i = 0; i < imax; i++) {
		for (l = 0; l < ExtremeRayArray.getSize(); l++) {
			if (AllVars[l].getId() == Lamda1_i[i].getId()) {
				Lamda1_iValue[i] = ExtremeRayArray[l];
			}
		}
	}
	for (i = 0; i < imax; i++) {
		for (l = 0; l < ExtremeRayArray.getSize(); l++) {
			if (AllVars[l].getId() == Lamda2_i[i].getId()) {
				Lamda2_iValue[i] = ExtremeRayArray[l];
			}
		}
	}
	for (i = 0; i < imax; i++) {
		for (j = 0; j < jmax; j++) {
			for (l = 0; l < ExtremeRayArray.getSize(); l++) {
				if (AllVars[l].getId() == Beta_ij[i][j].getId()) {
					Beta_ijValue[i][j] = ExtremeRayArray[l];
				}
			}
		}
	}
	for (i = 0; i < imax; i++) {
		for (j = 0; j < jmax; j++) {
			for (l = 0; l < ExtremeRayArray.getSize(); l++) {
				if (AllVars[l].getId() == Gamma_ij[i][j].getId()) {
					Gamma_ijValue[i][j] = ExtremeRayArray[l];
				}
			}
		}
	}

	return 0;
}
//int GetExtremePointOfDSP(IloCplex cplexDualSlave_ptr) {
//	//---------------------Get an extreme point of DUAL SLAVE problem--------------------
//	/*
//	for (i=0;i<imax;i++){
//	for (j=0;j<jmax;j++){
//	for (t=0;t<tmax;t++){
//	valsDualRangeSumXijt=cplexSlave_ptr.getDual(SumXijt[i][j][t]);
//	S2valsDualSumXijt[i][j][t]=valsDualRangeSumXijt;
//
//	valsDualRangeSumXijt=cplexSlave_ptr.getDual(DSumXijt[i][j][t]);
//	S22valsDualSumXijt[i][j][t]=valsDualRangeSumXijt;
//	}
//	}
//	}
//
//	for (k=0;k<kmax;k++){
//	for (j=0;j<jmax;j++){
//	for (t=0;t<tmax;t++){
//	valsDualRangeSumYkjt=cplexSlave_ptr.getDual(SumYkjt[k][j][t]);
//	S2valsDualSumYkjt[k][j][t]=valsDualRangeSumYkjt;
//
//	valsDualRangeSumYkjt=cplexSlave_ptr.getDual(DSumYkjt[k][j][t]);
//	S22valsDualSumYkjt[k][j][t]=valsDualRangeSumYkjt;
//	}
//	}
//	}
//
//	for (z=0;z<zmax;z++){
//	for (j=0;j<jmax;j++){
//	for (t=0;t<tmax;t++){
//	valsDualRangeCTIzjt=cplexSlave_ptr.getDual(CTIzjt[z][j][t]);
//	S2valsDualCTIzjt[z][j][t]=valsDualRangeCTIzjt;
//
//	valsDualRangeCTIzjt=cplexSlave_ptr.getDual(DCTIzjt[z][j][t]);
//	S22valsDualCTIzjt[z][j][t]=valsDualRangeCTIzjt;
//	}
//	}
//	}
//
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	valsDualRangeSum_Izt=cplexSlave_ptr.getDual(Sum_Izt[z][t]);
//	S2valsDualSum_Izt[z][t]=valsDualRangeSum_Izt;
//
//	}
//	}
//
//
//	for (i=0;i<imax;i++){
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	valsDualRangeCT1Fonctionement_Cizt=cplexSlave_ptr.getDual(CT1Fonctionement_Cizt[i][z][t]);
//	S2valsDualCT1Fonctionement_Cizt[i][z][t]=valsDualRangeCT1Fonctionement_Cizt;
//	}
//	}
//	}
//
//	for (i=0;i<imax;i++){
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	valsDualRangeCT2Fonctionement_Cizt=cplexSlave_ptr.getDual(CT2Fonctionement_Cizt[i][z][t]);
//	S2valsDualCT2Fonctionement_Cizt[i][z][t]=valsDualRangeCT2Fonctionement_Cizt;
//	}
//	}
//	}
//
//	for (k=0;k<kmax;k++){
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	valsDualRangeCT1Fonctionement_Dkzt=cplexSlave_ptr.getDual(CT1Fonctionement_Dkzt[k][z][t]);
//	S2valsDualCT1Fonctionement_Dkzt[k][z][t]=valsDualRangeCT1Fonctionement_Dkzt;
//	}
//	}
//	}
//
//	for (k=0;k<kmax;k++){
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	valsDualRangeCT2Fonctionement_Dkzt=cplexSlave_ptr.getDual(CT2Fonctionement_Dkzt[k][z][t]);
//	S2valsDualCT2Fonctionement_Dkzt[k][z][t]=valsDualRangeCT2Fonctionement_Dkzt;
//	}
//	}
//	}
//
//
//	for (z=0;z<zmax;z++){
//	for(j=0;j<jmax;j++){
//	for (t=0;t<tmax;t++){
//	valsDualRangeCT1Melzjt=cplexSlave_ptr.getDual(CT1Melzjt[z][j][t]);
//	S2valsDualCT1Melzjt[z][j][t]=valsDualRangeCT1Melzjt;
//	}
//	}
//	}
//
//	for (z=0;z<zmax;z++){
//	for(j=0;j<jmax;j++){
//	for (t=0;t<tmax;t++){
//	valsDualRangeCT2Melzjt=cplexSlave_ptr.getDual(CT2Melzjt[z][j][t]);
//	S2valsDualCT2Melzjt[z][j][t]=valsDualRangeCT2Melzjt;
//	}
//	}
//	}
//
//	for (i=0;i<imax;i++){
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	valsDualRangeSC2_Cizt=cplexSlave_ptr.getDual(SC2_Cizt[i][z][t]);
//	S2valsDualSC2_Cizt[i][z][t]=valsDualRangeSC2_Cizt;
//	}
//	}
//	}
//
//	for (k=0;k<kmax;k++){
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	valsDualRangeSD2_Dkzt=cplexSlave_ptr.getDual(SD2_Dkzt[k][z][t]);
//	S2valsDualSD2_Dkzt[k][z][t]=valsDualRangeSD2_Dkzt;
//	}
//	}
//	}
//
//	for (i=0;i<imax;i++){
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	valsDualRangeSC_Cizt=cplexSlave_ptr.getDual(SC_Cizt[i][z][t]);
//	S2valsDualSC_Cizt[i][z][t]=valsDualRangeSC_Cizt;
//	}
//	}
//	}
//
//	for (k=0;k<kmax;k++){
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	valsDualRangeSD_Dkzt=cplexSlave_ptr.getDual(SD_Dkzt[k][z][t]);
//	S2valsDualSD_Dkzt[k][z][t]=valsDualRangeSD_Dkzt;
//	}
//	}
//	}
//	*/
//	return 0;
//}
//int AddBendersOptimalityCutToMaster(IloExpr expr101, IloModel modelMaster_ptr) {
//	//--------------ADD BENDERS  CUT TO MASTER----------------
//	//If FeasOrOpt=0, then a FEASIBILITY CUT is added
//	//If FeasOrOpt=1, then a OPTIMALITY CUT is added
//	char MasterCut[60];
//	sprintf(MasterCut, "OptimalityCut(iter%d)", loop);
//	BDOptCuts++;
//	double LB101 = 0, UB101 = IloInfinity;
//	IloRange CTMaster(env, LB101, expr101, UB101, MasterCut);
//	BendersCuts.add(CTMaster);
//	modelMaster_ptr.add(CTMaster);
//	CutsPerIteration++;
//
//	return 0;
//}
int CreateBendersCut(int FeasOrOpt, IloExpr expr101, IloNumVarArray X_vj, IloNumVarArray X_mj, IloNumVarArray Zn) {
	//---------CREATION OF BENDERS CUT--------------- 
	//If FeasOrOpt=0, then a FEASIBILITY CUT is created
	//If FeasOrOpt=1, then a OPTIMALITY CUT is created
	for (i = 0; i < imax; i++) {
		for (j = 0; j < jmax; j++) {
			expr101 += Beta_ijValue[i][j] * X_vj[j];
			expr101 += Gamma_ijValue[i][j] * X_mj[j];
		}
		expr101 += Lamda1_iValue[i] + Lamda2_iValue[i];
	}

	if (FeasOrOpt == 1) {//then create an Optimality cut
		for (n = 0; n < 1; n++) {
			expr101 -= Zn[n];
		}
	}

	return 0;
}
int AddBendersCutToMaster(IloEnv env, int FeasOrOpt, IloExpr expr101, int loop, IloModel modelMaster_ptr, IloRangeArray BendersCuts) {
	//--------------ADD BENDERS  CUT TO MASTER----------------
	//If FeasOrOpt=0, then a FEASIBILITY CUT is added
	//If FeasOrOpt=1, then a OPTIMALITY CUT is added
	char MasterCut[90];

	if (FeasOrOpt == 0) {
		sprintf(MasterCut, "FeasibilityCutFromClassicalDSP(iter%d)", loop);
		BDFeasCuts++;
	}
	else if (FeasOrOpt == 1) {
		sprintf(MasterCut, "OptimalityCutFromClassicalDSP(iter%d)", loop);
		BDOptCuts++;
	}

	double LB101 = 0, UB101 = IloInfinity;
	IloRange CTMaster(env, LB101, expr101, UB101, MasterCut);
	BendersCuts.add(CTMaster);
	modelMaster_ptr.add(CTMaster);
	CutsPerIteration++;

	return 0;
}
int PrintBeta() {
	std::ostringstream Coef_Beta_ij;
	Coef_Beta_ij << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\ClassBD\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\ClassBD - Beta_ij.txt";
	std::string FileNameCoef_Beta_ij = Coef_Beta_ij.str();
	std::ofstream fsCoef_Beta_ij;
	fsCoef_Beta_ij.open(FileNameCoef_Beta_ij.c_str(), std::ios::out);
	for (j = 0; j < jmax; j++) {
		for (i = 0; i < imax; i++) {
			fsCoef_Beta_ij << Beta_ijValue[i][j] << "\t";
		}
		fsCoef_Beta_ij << std::endl;
	}
	fsCoef_Beta_ij.close();


	std::ostringstream Coef_Lamda1_i;
	Coef_Lamda1_i << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\ClassBD\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\ClassBD - Lamda1_i.txt";
	std::string FileNameCoef_Lamda1_i = Coef_Lamda1_i.str();
	std::ofstream fsCoef_Lamda1_i;
	fsCoef_Lamda1_i.open(FileNameCoef_Lamda1_i.c_str(), std::ios::out);
	for (j = 0; j < jmax; j++) {
		fsCoef_Lamda1_i << Lamda1_iValue[j] << "\t";
	}
	fsCoef_Lamda1_i.close();
	return 0;
}
int BendersIteration(IloObjective Dual_objective_ptr, IloEnv env, IloModel modelMaster_ptr, IloModel modelDualSlave_ptr, IloNumVarArray X_vj, IloNumVarArray X_mj, IloNumVarArray Zn, IloNum SlackValuesMasterCons, IloNumArray SlackValues, IloRangeArray Con_Master_1n, IloRangeArray Con_Master_2n, IloRangeArray Con_Master_3i, IloRangeArray BendersCuts, IloNumVarArray Lamda1_i, IloNumVarArray Lamda2_i, IloNumVarMatrix2x2 Beta_ij, IloNumVarMatrix2x2 Gamma_ij, IloNumArray ExtremeRayArray, IloNumVarArray AllVars, IloRangeMatrix2x2 Con_Slave_1ij, IloRangeMatrix2x2 Con_Slave_2ij, IloNumArray Dual_Obj_Coefs) {

	bool InfeasibleMaster = false;
	int status, startMaster, stopMaster, startSlave, stopSlave;
	int CoveredVariables;
	int DualStatus;
	IloCplex cplexDualSlave_ptr(env);
	IloCplex cplexMaster_ptr(env);

	cplexDualSlave_ptr.extract(modelDualSlave_ptr);
	cplexDualSlave_ptr.exportModel("modelDualSlave.lp");

	cplexMaster_ptr.extract(modelMaster_ptr);
	cplexMaster_ptr.exportModel("modelMaster1.lp");

	double DTransposeY = 0, DualSlaveObjFunction = 0, PrimalSlaveObjFunction = 0;
	double BestSlaveObj = 100;
	for (i = 0; i < imax; i++) {
		status_dual[i] = 0;//status_dual=1 feasible, status_dual=0 unbounded
	}
	LowerBoundArray.clear();
	UpperBoundArray.clear();
	LowerBoundGlobalArray.clear();
	dTy.clear();
	zCurrent.clear();
	cTx.clear();
	bTu.clear();
	BestPrimalSlaveObjSoFar.clear();
	BestDualSlaveObjSoFar.clear();
	Time.clear();
	SlackValuesOfBendersCuts.clear();
	SlackValuesOfMainMasterCons.clear();
	NoOfCutsInEachIteration.clear();

	BDFeasCuts = 0;
	BDOptCuts = 0;
	DurationMaster = 0;
	DurationSlave = 0;
	loop = 0;
	UpperBound = 10000000;
	LowerBound = -10000000;
	LowerBoundGlobal = -10000000;

	while (Gap > epsilon && loop < MaxIterations && ((clock() - start) / CLOCKS_PER_SEC) < MaxDuration) {
		loop++;
		//cout << "-----------------" << endl;
		//cout << "Iteration =" << loop << endl;
		//cout << "-----------------" << endl;
		CutsPerIteration = 0;
		CoveredVariables = 0;
		DTransposeY = 0;
		startMaster = clock();
		status = Solve_Master(env, modelMaster_ptr, cplexMaster_ptr, X_vj, X_mj, Zn, &DTransposeY, &InfeasibleMaster);
		if (status != 0) {
			Found_Error("Solve_Master");
			return -1;
		}
		stopMaster = clock();
		DurationMaster += (long double)(stopMaster - startMaster) / CLOCKS_PER_SEC;
		if (InfeasibleMaster == true) {
			break;
		}

		/*status = Get_Slack_Values(cplexMaster_ptr, SlackValuesMasterCons, SlackValues, Con_Master_1n, Con_Master_2n, BendersCuts);
		if (status != 0) {
			Found_Error("Get_Slack_Values");
			return -1;
		}*/

		status = UpdateDualSlaveObjective(env, Lamda1_i, Lamda2_i, Beta_ij, Gamma_ij, Dual_Obj_Coefs, Dual_objective_ptr);
		if (status != 0) {
			Found_Error("UpdateDualSlaveObjective");
			return -1;
		}
		startSlave = clock();
		status = Solve_Dual_Slave(env, modelDualSlave_ptr, cplexDualSlave_ptr, Lamda1_i, Lamda2_i, Beta_ij, Gamma_ij, Dual_objective_ptr);
		if (status != 0) {
			Found_Error("Solve_Dual_Slave");
			return -1;
		}
		stopSlave = clock();
		DurationSlave += (long double)(stopSlave - startSlave) / CLOCKS_PER_SEC;
		DualStatus = cplexDualSlave_ptr.getStatus();


		if (DualStatus == 4) { //---------IF DUAL SLAVE IS UNBOUNDED-----

			status = Dual_Slave_Unbounded(env, &DualSlaveObjFunction, &PrimalSlaveObjFunction);
			if (status != 0) {
				Found_Error("Dual_Slave_Unbounded");
				return -1;
			}
			status = GetExtremeRayOfDSP(cplexDualSlave_ptr, ExtremeRayArray, Lamda1_i, Lamda2_i, Beta_ij, Gamma_ij, AllVars);
			if (status != 0) {
				Found_Error("GetExtremeRayOfDSP");
				return -1;
			}
			IloExpr expr101(env);
			status = CreateBendersCut(0, expr101, X_vj, X_mj, Zn);//if =0, then creates feasibility cut
			if (status != 0) {
				Found_Error("CreateBendersFeasibilityCut");
				return -1;
			}
			status = AddBendersCutToMaster(env, 0, expr101, loop, modelMaster_ptr, BendersCuts);//if =0, then adds feasibility cut
			if (status != 0) {
				Found_Error("AddBendersFeasibilityCutToMaster");
				return -1;
			}
			expr101.end();
		}//Fin de IF QUI A TROUVE QUE SLAVE 1 EST INFEASIBLE

		else { //------------- IF SLAVE PROBLEM IS FEASIBLE------------

			status = Dual_Slave_Bounded(env, cplexDualSlave_ptr, &DTransposeY, &DualSlaveObjFunction, &PrimalSlaveObjFunction, loop, Con_Slave_1ij, Con_Slave_2ij);
			if (status != 0) {
				Found_Error("Dual_Slave_Bounded");
				return -1;
			}
			/*status = PrintBeta();
			if (status != 0) {
				Found_Error("PrintBeta");
				return -1;
			}*/
			IloExpr expr101(env);
			status = CreateBendersCut(1, expr101, X_vj, X_mj, Zn);//if =1, then creates optimality cut
			if (status != 0) {
				Found_Error("CreateBendersOptimalityCut");
				return -1;
			}
			status = AddBendersCutToMaster(env, 1, expr101, loop, modelMaster_ptr, BendersCuts);//if =1, then adds optimality cut
			if (status != 0) {
				Found_Error("AddBendersOptimalityCutToMaster");
				return -1;
			}
			expr101.end();
		}//end of else if (DualStatus==4)


		cTx.push_back(PrimalSlaveObjFunction);
		bTu.push_back(DualSlaveObjFunction);
		BestPrimalSlaveObjSoFar.push_back(OptimalPrimalSlaveObjFunction);
		BestDualSlaveObjSoFar.push_back(OptimalDualSlaveObjFunction);
		LowerBoundArray.push_back(LowerBound);
		UpperBoundArray.push_back(UpperBound);
		LowerBoundGlobalArray.push_back(LowerBoundGlobal);
		Time.push_back((long double)(clock() - start) / CLOCKS_PER_SEC);
		NoOfCutsInEachIteration.push_back(CutsPerIteration);
		Gap = (UpperBound - LowerBoundGlobal) / UpperBound;
		/*
		if(ThetaValue!=0){
		cout<<"OptimalThetaValue="<<OptimalThetaValue<<endl;
		}
		if(DTransposeY!=0){
		cout<<"DTransposeY="<<DTransposeY<<endl;
		}
		if(SlaveObjFunction!=0){
		cout<<"SlaveObjFunction="<<SlaveObjFunction<<endl;
		}
		if(OptimalSlaveObjFunction!=0){
		cout<<"OptimalSlaveObjFunction="<<OptimalSlaveObjFunction<<endl;
		}
		*/
		//cout << "UpperBound=" << UpperBound << endl;
		//cout << "LowerBoundGlobal=" << LowerBoundGlobal << endl;
		//cout << "Gap=" << Gap * 100 << "%" << endl;
		//cout<<"UpperBound="<<UpperBound<<endl;
		//cout << "-----------------" << endl;
		//cout << "------END OF ITERATION--------" << endl;

		////-----------------------------
		//std::ostringstream os;
		//os << "C:\\Results_CrudeOil\\PureBENDERSDual\\PureBENDERSDual - CurrentSolution.txt";
		//std::string FileName = os.str();

		//std::ofstream fsOptimalSolution;
		//fsOptimalSolution.open(FileName.c_str(), std::ios::out);
		////fsOptimalSolution << "TotalSolutionTime= " << Duration << " seconds " << std::endl;
		//if ((LowerBoundGlobal - LowerBound) / LowerBoundGlobal>0) {
		//	fsOptimalSolution << "OptimalityGap= " << (LowerBoundGlobal - LowerBound) / LowerBoundGlobal << std::endl;
		//}
		//else {
		//	fsOptimalSolution << "OptimalityGap= 0" << std::endl;
		//}
		//fsOptimalSolution << "OptimalObjFunction= " << LowerBoundGlobal << std::endl;
		//fsOptimalSolution << "OptimalMasterObjFunction= " << DTransposeY << std::endl;
		//fsOptimalSolution << "OptimalPrimalSlaveObjFunction= " << PrimalSlaveObjFunction << std::endl;
		//fsOptimalSolution << "OptimalDualSlaveObjFunction= " << DualSlaveObjFunction << std::endl;
		//fsOptimalSolution << "----------------------------------" << std::endl;
		//if (OptimalThetaValue>0.01) {
		//	fsOptimalSolution << "OptimalThetaValue= " << ThetaValue << std::endl;
		//}
		//fsOptimalSolution << "----------------------------------" << std::endl;
		//fsOptimalSolution << "TotalNumberOfFeasibilityCuts= " << BDFeasCuts << std::endl;
		//fsOptimalSolution << "TotalNumberOfOptimalityCuts= " << BDOptCuts << std::endl;
		//fsOptimalSolution << "TotalNumberOfMasterVariables= " << NoOfMasterVars << std::endl;
		//fsOptimalSolution << "TotalNumberOfSlaveVariables= " << NoOfSlaveVars << std::endl;
		//fsOptimalSolution << "TotalNumberOfMasterConstraints= " << NoOfMasterCons << std::endl;
		//fsOptimalSolution << "TotalNumberOfSlaveConstraints= " << NoOfSlaveCons << std::endl;
		//fsOptimalSolution << "----------------------------------" << std::endl;
		//for (i = 0; i<imax; i++) {
		//	for (z = 0; z<zmax; z++) {
		//		for (t = 0; t<tmax; t++) {
		//			if (CiztValue[i][z][t] >= 0.01) {
		//				fsOptimalSolution << "OptimalCiztValue" << "[" << i << "]" << "[" << z << "]" << "[" << t << "]" << "=" << CiztValue[i][z][t] << std::endl;
		//			}
		//		}
		//	}
		//}
		//fsOptimalSolution << "----------------------------------" << std::endl;

		//for (k = 0; k<kmax; k++) {
		//	for (z = 0; z<zmax; z++) {
		//		for (t = 0; t<tmax; t++) {
		//			if (DkztValue[k][z][t] >= 0.01) {
		//				fsOptimalSolution << "OptimalDkztValue" << "[" << k << "]" << "[" << z << "]" << "[" << t << "]" << "=" << DkztValue[k][z][t] << std::endl;
		//			}
		//		}
		//	}
		//}
		//fsOptimalSolution << "----------------------------------" << std::endl;

		//for (z = 0; z<zmax; z++) {
		//	for (j = 0; j<jmax; j++) {
		//		for (t = 0; t<tmax; t++) {
		//			if (FzjtValue[z][j][t] >= 0.01) {
		//				fsOptimalSolution << "OptimalFzjtValue" << "[" << z << "]" << "[" << j << "]" << "[" << t << "]" << "=" << FzjtValue[z][j][t] << std::endl;
		//			}
		//		}
		//	}
		//}
		//fsOptimalSolution << "----------------------------------" << std::endl;

		//for (i = 0; i<imax; i++) {
		//	for (z = 0; z<zmax; z++) {
		//		for (t = 0; t<tmax; t++) {
		//			if (SCiztValue[i][z][t] >= 0.01) {
		//				fsOptimalSolution << "OptimalSCiztValue" << "[" << i << "]" << "[" << z << "]" << "[" << t << "]" << "=" << SCiztValue[i][z][t] << std::endl;
		//			}
		//		}
		//	}
		//}
		//fsOptimalSolution << "----------------------------------" << std::endl;

		//for (k = 0; k<kmax; k++) {
		//	for (z = 0; z<zmax; z++) {
		//		for (t = 0; t<tmax; t++) {
		//			if (SDkztValue[k][z][t] >= 0.01) {
		//				fsOptimalSolution << "OptimalSDkztValue" << "[" << k << "]" << "[" << z << "]" << "[" << t << "]" << "=" << SDkztValue[k][z][t] << std::endl;
		//			}
		//		}
		//	}
		//}
		//fsOptimalSolution << "----------------------------------" << std::endl;

		//for (i = 0; i<imax; i++) {
		//	for (z = 0; z<zmax; z++) {
		//		for (j = 0; j<jmax; j++) {
		//			for (t = 0; t<tmax; t++) {
		//				if (XizjtValue[i][z][j][t] >= 0.01) {
		//					fsOptimalSolution << "OptimalXizjtValue" << "[" << i << "]" << "[" << z << "]" << "[" << j << "]" << "[" << t << "]" << "=" << XizjtValue[i][z][j][t] << std::endl;
		//				}
		//			}
		//		}
		//	}
		//}
		//fsOptimalSolution << "----------------------------------" << std::endl;

		//for (z = 0; z<zmax; z++) {
		//	for (k = 0; k<kmax; k++) {
		//		for (j = 0; j<jmax; j++) {
		//			for (t = 0; t<tmax; t++) {
		//				if (YzkjtValue[z][k][j][t] >= 0.01) {
		//					fsOptimalSolution << "OptimalYzkjtValue" << "[" << z << "]" << "[" << k << "]" << "[" << j << "]" << "[" << t << "]" << "=" << YzkjtValue[z][k][j][t] << std::endl;
		//				}
		//			}
		//		}
		//	}
		//}
		//fsOptimalSolution << "----------------------------------" << std::endl;


		//for (z = 0; z<zmax; z++) {
		//	for (j = 0; j<jmax; j++) {
		//		for (t = 0; t<tmax; t++) {
		//			if (IzjtValue[z][j][t] >= 0.01) {
		//				fsOptimalSolution << "OptimalIzjtValue" << "[" << z << "]" << "[" << j << "]" << "[" << t << "]" << "=" << IzjtValue[z][j][t] << std::endl;
		//			}
		//		}
		//	}
		//}

		//fsOptimalSolution.close();

		//---------------------



	}//end of loop

	return 0;
}//end of BendersIteration

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
	os << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\ClassBD\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\ClassBD - OptimalSolution.txt";
	std::string FileName = os.str();

	std::ofstream fsOptimalSolution;
	fsOptimalSolution.open(FileName.c_str(), std::ios::out);
	fsOptimalSolution << "TotalSolutionTime= " << Duration << " seconds " << std::endl;
	fsOptimalSolution << "MasterSolutionTime= " << DurationMaster << " seconds " << std::endl;
	fsOptimalSolution << "SlaveSolutionTime= " << DurationSlave << " seconds " << std::endl;
	fsOptimalSolution << "TotalIterations= " << loop << std::endl;
	fsOptimalSolution << "OptimalityGap= " << Gap << std::endl;
	fsOptimalSolution << "OptimalObjFunction= " << OptimalOriginalObjFunction << std::endl;
	fsOptimalSolution << "TotalVansUsed= " << TotalVansUsed << std::endl;
	fsOptimalSolution << "TotalMotorcyclesUsed= " << TotalMotorcyclesUsed << std::endl;
	fsOptimalSolution << "OptimalMasterObjFunction= " << OptimalMasterObjFunction << std::endl;
	fsOptimalSolution << "OptimalPrimalSlaveObjFunction= " << OptimalPrimalSlaveObjFunction << std::endl;
	fsOptimalSolution << "OptimalDualSlaveObjFunction= " << OptimalDualSlaveObjFunction << std::endl;
	fsOptimalSolution << "----------------------------------" << std::endl;
	if (OptimalThetaValue > 0.01) {
		fsOptimalSolution << "OptimalThetaValue= " << OptimalThetaValue << std::endl;
	}
	fsOptimalSolution << "----------------------------------" << std::endl;
	fsOptimalSolution << "TotalNumberOfFeasibilityCuts= " << BDFeasCuts << std::endl;
	fsOptimalSolution << "TotalNumberOfOptimalityCuts= " << BDOptCuts << std::endl;
	fsOptimalSolution << "TotalNumberOfMasterVariables= " << NoOfMasterVars << std::endl;
	fsOptimalSolution << "TotalNumberOfPrimalSlaveVariables= " << NoOfPrimalSlaveVars << std::endl;
	fsOptimalSolution << "TotalNumberOfMasterConstraints= " << NoOfMasterCons << std::endl;
	fsOptimalSolution << "TotalNumberOfPrimalSlaveConstraints= " << NoOfPrimalSlaveCons << std::endl;
	fsOptimalSolution << "----------------------------------" << std::endl;

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
	fsOptimalSolution << "----------------------------------" << std::endl;
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
	}
	fsOptimalSolution.close();


	std::ostringstream LowerBound;
	LowerBound << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\ClassBD\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\ClassBD - LowerBound.txt";
	std::string FileNameLB = LowerBound.str();
	std::ofstream fsLowerBound;
	fsLowerBound.open(FileNameLB.c_str(), std::ios::out);
	for (i = 0; i < LowerBoundArray.size(); i++) {
		fsLowerBound << LowerBoundArray.at(i) << std::endl;
	}
	fsLowerBound.close();

	std::ostringstream UpperBound;
	UpperBound << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\ClassBD\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\ClassBD - UpperBound.txt";
	std::string FileNameUB = UpperBound.str();
	std::ofstream fsUpperBound;
	fsUpperBound.open(FileNameUB.c_str(), std::ios::out);
	for (i = 0; i < UpperBoundArray.size(); i++) {
		fsUpperBound << UpperBoundArray.at(i) << std::endl;
	}
	fsUpperBound.close();

	std::ostringstream LowerBoundGlobal;
	LowerBoundGlobal << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\ClassBD\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\ClassBD - LowerBoundGlobal.txt";
	std::string FileNameUBG = LowerBoundGlobal.str();
	std::ofstream fsLowerBoundGlobal;
	fsLowerBoundGlobal.open(FileNameUBG.c_str(), std::ios::out);
	for (i = 0; i < LowerBoundGlobalArray.size(); i++) {
		fsLowerBoundGlobal << LowerBoundGlobalArray.at(i) << std::endl;
	}
	fsLowerBoundGlobal.close();


	std::ostringstream dTransY;
	dTransY << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\ClassBD\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\ClassBD - DTrasnposeY.txt";
	std::string FileNameDTY = dTransY.str();
	std::ofstream fsdTransY;
	fsdTransY.open(FileNameDTY.c_str(), std::ios::out);
	for (i = 0; i < dTy.size(); i++) {
		fsdTransY << dTy.at(i) << std::endl;
	}
	fsdTransY.close();

	std::ostringstream cTransX;
	cTransX << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\ClassBD\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\ClassBD - CTrasnposeX.txt";
	std::string FileNameCTX = cTransX.str();
	std::ofstream fscTransX;
	fscTransX.open(FileNameCTX.c_str(), std::ios::out);
	for (i = 0; i < cTx.size(); i++) {
		fscTransX << cTx.at(i) << std::endl;
	}
	fscTransX.close();

	std::ostringstream bTransU;
	bTransU << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\ClassBD\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\ClassBD - BTrasnposeU.txt";
	std::string FileNameBTU = bTransU.str();
	std::ofstream fsbTransU;
	fsbTransU.open(FileNameBTU.c_str(), std::ios::out);
	for (i = 0; i < bTu.size(); i++) {
		fsbTransU << bTu.at(i) << std::endl;
	}
	fsbTransU.close();

	std::ostringstream CurrentTheta;
	CurrentTheta << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\ClassBD\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\ClassBD - CurrentTheta.txt";
	std::string FileNameCurrentTheta = CurrentTheta.str();
	std::ofstream fsCurrentTheta;
	fsCurrentTheta.open(FileNameCurrentTheta.c_str(), std::ios::out);
	for (i = 0; i < zCurrent.size(); i++) {
		fsCurrentTheta << zCurrent.at(i) << std::endl;
	}
	fsCurrentTheta.close();

	std::ostringstream BestPrimalSlaveObj;
	BestPrimalSlaveObj << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\ClassBD\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\ClassBD - BestPrimalSlaveObjSoFar.txt";
	std::string FileNameBPSO = BestPrimalSlaveObj.str();
	std::ofstream fsBestPrimalSlaveObj;
	fsBestPrimalSlaveObj.open(FileNameBPSO.c_str(), std::ios::out);
	for (i = 0; i < BestPrimalSlaveObjSoFar.size(); i++) {
		fsBestPrimalSlaveObj << BestPrimalSlaveObjSoFar.at(i) << std::endl;
	}
	fsBestPrimalSlaveObj.close();

	std::ostringstream BestDualSlaveObj;
	BestDualSlaveObj << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\ClassBD\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\ClassBD - BestDualSlaveObjSoFar.txt";
	std::string FileNameBDSO = BestDualSlaveObj.str();
	std::ofstream fsBestDualSlaveObj;
	fsBestDualSlaveObj.open(FileNameBDSO.c_str(), std::ios::out);
	for (i = 0; i < BestDualSlaveObjSoFar.size(); i++) {
		fsBestDualSlaveObj << BestDualSlaveObjSoFar.at(i) << std::endl;
	}
	fsBestDualSlaveObj.close();



	std::ostringstream TimePath;
	TimePath << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\ClassBD\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\ClassBD - Time.txt";
	std::string FileNameTime = TimePath.str();
	std::ofstream fsTime;
	fsTime.open(FileNameTime.c_str(), std::ios::out);
	for (i = 0; i < Time.size(); i++) {
		fsTime << Time.at(i) << std::endl;
	}
	fsTime.close();

	std::ostringstream DataDistance;
	DataDistance << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\ClassBD\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\ClassBD - Distance.txt";
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
	Data << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\ClassBD\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\ClassBD - Data.txt";
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
	//SlackVals << "C:\\Results_Ambulance\\ClassBD\\ClassBD - SlackValuesBendersCuts.txt";
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
	std::ostringstream SlackValsMasterCons;
	SlackValsMasterCons << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\ClassBD\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\ClassBD - SlackValuesMainMasterCons.txt";
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
				IloModel modelDualSlave(env);
				IloModel modelMaster(env);

				//------Declare Decision Variables----------
				IloNumVarArray X_vj(env, 0);
				IloNumVarArray X_mj(env, 0);
				IloNumVarArray Zn(env, 0);
				//------Declare Dual Slave Decision Variables----------
				IloNumVarArray Lamda1_i(env, 0);
				IloNumVarArray Lamda2_i(env, 0);
				IloNumVarMatrix2x2 Beta_ij(env, 0);
				IloNumVarMatrix2x2 Gamma_ij(env, 0);

				IloNumVarArray AllVars(env, 0);

				//--------Declare Master constraints-------------
				IloRangeArray Con_Master_1n(env, 0);
				IloRangeArray Con_Master_2n(env, 0);
				IloRangeArray Con_Master_3i(env, 0);
				//--------Declare Dual Slave constraints-------------
				IloRangeMatrix2x2 Con_Slave_1ij(env, 0);
				IloRangeMatrix2x2 Con_Slave_2ij(env, 0);
				//--------Declare Dual Objective function-------------
				IloObjective Dual_objective(env, imax);


				//--------Declare Array of Benders Cuts Added in Master Problem-------------
				IloRangeArray BendersCuts(env, 0);

				//--------Declare dual variables of each constraint----------------
				IloNumArray ExtremeRayArray(env, 0);
				IloNumArray SlackValues(env, 0);
				IloNum SlackValuesMasterCons = 0;
				IloNumArray Dual_Obj_Coefs(env, imax);

				start = clock();

				status = load_data();
				if (status != 0) {
					Found_Error("load_data");
					return -1;
				}

				status = do_master(env, modelMaster, X_vj, X_mj, Zn, AllVars, Con_Master_1n, Con_Master_2n, Con_Master_3i);
				if (status != 0) {
					Found_Error("do_master");
					return -1;
				}

				status = do_dual_slave(env, modelDualSlave, Lamda1_i, Lamda2_i, Beta_ij, Gamma_ij, AllVars, Con_Slave_1ij, Con_Slave_2ij);
				if (status != 0) {
					Found_Error("do_dual_slave");
					return -1;
				}

				Dual_objective = IloAdd(modelDualSlave, IloMinimize(env));

				status = BendersIteration(Dual_objective, env, modelMaster, modelDualSlave, X_vj, X_mj, Zn, SlackValuesMasterCons, SlackValues, Con_Master_1n, Con_Master_2n, Con_Master_3i, BendersCuts, Lamda1_i, Lamda2_i, Beta_ij, Gamma_ij, ExtremeRayArray, AllVars, Con_Slave_1ij, Con_Slave_2ij, Dual_Obj_Coefs);
				if (status != 0) {
					Found_Error("BendersIteration");
					return -1;
				}
				stop = clock();
				Duration = (long double)(stop - start) / CLOCKS_PER_SEC;

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
			printf("Execution time = %Lf seconds\n", Duration);
		}
	}
	return 0;

} //End main