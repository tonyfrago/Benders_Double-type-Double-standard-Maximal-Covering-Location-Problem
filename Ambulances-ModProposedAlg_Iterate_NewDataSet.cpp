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
int Importance_i[imax];
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
int MaxFeasibilityCutsAdded = imax;//Max No of Feasibility Cuts added in an iteration
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

float X_vjValue[jmax];
float X_mjValue[jmax];
float Y_vijValue[imax][jmax];
float Y_mijValue[imax][jmax];
float Lamda1_iValue[imax];
float Lamda2_iValue[imax];
float Beta_ijValue[imax][jmax];
float Gamma_ijValue[imax][jmax];
float ThetaValue = 0;

float OptimalX_vjValue[jmax];
float OptimalX_mjValue[jmax];
float OptimalY_vijValue[imax][jmax];
float OptimalY_mijValue[imax][jmax];
float OptimalLamda1_iValue[imax];
float OptimalLamda2_iValue[imax];
float OptimalBeta_ijValue[imax][jmax];
float OptimalGamma_ijValue[imax][jmax];
float OptimalThetaValue = 0;

float OriginalObjFunction = 0;
float MasterObjFunction = 0;
float PrimalSlaveObjFunction = 0;
float DualSlaveObjFunction = 0;

float OptimalOriginalObjFunction = 0;
float OptimalMasterObjFunction = 0;
float OptimalPrimalSlaveObjFunction = 0;
float OptimalDualSlaveObjFunction = 0;
float OptimalObjFunctionFirstTerm = 0;
float OptimalObjFunctionSecondTerm = 0;



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
vector <double> OptCutCoefs;


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
	/*for (i = 0; i < imax; i++) {
		Importance_i[i] = Importance_i[i]*10;
	}*/

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
	//Weight = Weight * 1000;
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
	bool FeasCutForNodeAdded_i[imax];
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
	/*for (j = 0; j < jmax; j++) {
		expr1 -= X_vj[j]+X_mj[j];
	}*/

	modelMaster.add(IloMaximize(env, expr1));
	expr1.end();

	return 0;
}
//int do_dual_slave() {
//	NoOfSlaveVars = 0;
//	NoOfSlaveCons = 0;
//
//
//
//
//	//--------------------------- DUAL SLAVE PROBLEM OF LOCATION i (DSPi) ----------------------------------
//	//------------------------------------------------------------------------------
//	//--------------------------- Slave Dual Variables ---------------------------
//	//--------------------------- Decision Variable U1ijt ---------------------------
//
//	for (i = 0; i<imax; i++) {
//		IloNumVarMatrix2x2 U1jt(env, 0);
//		for (j = 0; j<jmax; j++) {
//			IloNumVarArray U1t(env, 0);
//			for (t = 0; t<tmax; t++) {
//				char Dual1[70];
//				sprintf(Dual1, "U1ijt(i%d,j%d,t%d)", i, j, t);
//				IloNumVar U1(env, -IloInfinity, IloInfinity, ILOFLOAT, Dual1);
//				NoOfSlaveVars++;
//				U1t.add(U1);
//				AllVars.add(U1);
//			}
//			U1jt.add(U1t);
//		}
//		U1ijt.add(U1jt);
//	}
//
//	//--------------------------- Decision Variable U2kjt --------------------------
//	for (k = 0; k<kmax; k++) {
//		IloNumVarMatrix2x2 U2jt(env, 0);
//		for (j = 0; j<jmax; j++) {
//			IloNumVarArray U2t(env, 0);
//			for (t = 0; t<tmax; t++) {
//				char Dual2[70];
//				sprintf(Dual2, "U2kjt(k%d,j%d,t%d)", k, j, t);
//				IloNumVar U2(env, -IloInfinity, IloInfinity, ILOFLOAT, Dual2);
//				NoOfSlaveVars++;
//				U2t.add(U2);
//				AllVars.add(U2);
//			}
//			U2jt.add(U2t);
//		}
//		U2kjt.add(U2jt);
//	}
//
//	//--------------------------- Decision Variable U3zjt --------------------------
//
//	for (z = 0; z<zmax; z++) {
//		IloNumVarMatrix2x2 U3jt(env, 0);
//		for (j = 0; j<jmax; j++) {
//			IloNumVarArray U3t(env, 0);
//			for (t = 0; t<tmax; t++) {
//				char Dual3[70];
//				sprintf(Dual3, "U3zjt(z%d,j%d,t%d)", z, j, t);
//				IloNumVar U3(env, -IloInfinity, IloInfinity, ILOFLOAT, Dual3);
//				NoOfSlaveVars++;
//				U3t.add(U3);
//				AllVars.add(U3);
//			}
//			U3jt.add(U3t);
//		}
//		U3zjt.add(U3jt);
//	}
//
//
//	//-------------- Decision Variable U4zt ---------------------------------------
//
//	for (z = 0; z<zmax; z++) {
//		IloNumVarArray U4t(env, 0);
//		for (t = 0; t<tmax; t++) {
//			char Dual4[70];
//			sprintf(Dual4, "U4zt(z%d,t%d)", z, t);
//			IloNumVar U4(env, 0, IloInfinity, ILOFLOAT, Dual4);
//			NoOfSlaveVars++;
//			U4t.add(U4);
//			AllVars.add(U4);
//		}
//		U4zt.add(U4t);
//	}
//
//
//	//-------------- Decision Variable U5izt ---------------------------------------
//
//	for (i = 0; i<imax; i++) {
//		IloNumVarMatrix2x2 U5zt(env, 0);
//		for (z = 0; z<zmax; z++) {
//			IloNumVarArray U5t(env, 0);
//			for (t = 0; t<tmax; t++) {
//				char Dual5[70];
//				sprintf(Dual5, "U5izt(i%d,z%d,t%d)", i, z, t);
//				IloNumVar U5(env, 0, IloInfinity, ILOFLOAT, Dual5);
//				NoOfSlaveVars++;
//				U5t.add(U5);
//				AllVars.add(U5);
//			}
//			U5zt.add(U5t);
//		}
//		U5izt.add(U5zt);
//	}
//
//	//-------------- Decision Variable U6izt ---------------------------------------
//
//	for (i = 0; i<imax; i++) {
//		IloNumVarMatrix2x2 U6zt(env, 0);
//		for (z = 0; z<zmax; z++) {
//			IloNumVarArray U6t(env, 0);
//			for (t = 0; t<tmax; t++) {
//				char Dual6[70];
//				sprintf(Dual6, "U6izt(i%d,z%d,t%d)", i, z, t);
//				IloNumVar U6(env, 0, IloInfinity, ILOFLOAT, Dual6);
//				NoOfSlaveVars++;
//				U6t.add(U6);
//				AllVars.add(U6);
//			}
//			U6zt.add(U6t);
//		}
//		U6izt.add(U6zt);
//	}
//
//	//-------------- Decision Variable U7kzt ---------------------------------------
//	for (k = 0; k<kmax; k++) {
//		IloNumVarMatrix2x2 U7zt(env, 0);
//		for (z = 0; z<zmax; z++) {
//			IloNumVarArray U7t(env, 0);
//			for (t = 0; t<tmax; t++) {
//				char Dual7[70];
//				sprintf(Dual7, "U7kzt(k%d,z%d,t%d)", k, z, t);
//				IloNumVar U7(env, 0, IloInfinity, ILOFLOAT, Dual7);
//				NoOfSlaveVars++;
//				U7t.add(U7);
//				AllVars.add(U7);
//			}
//			U7zt.add(U7t);
//		}
//		U7kzt.add(U7zt);
//	}
//
//	//-------------- Decision Variable U8kzt ---------------------------------------
//
//	for (k = 0; k<kmax; k++) {
//		IloNumVarMatrix2x2 U8zt(env, 0);
//		for (z = 0; z<zmax; z++) {
//			IloNumVarArray U8t(env, 0);
//			for (t = 0; t<tmax; t++) {
//				char Dual8[70];
//				sprintf(Dual8, "U8kzt(k%d,z%d,t%d)", k, z, t);
//				IloNumVar U8(env, 0, IloInfinity, ILOFLOAT, Dual8);
//				NoOfSlaveVars++;
//				U8t.add(U8);
//				AllVars.add(U8);
//			}
//			U8zt.add(U8t);
//		}
//		U8kzt.add(U8zt);
//	}
//
//	//-------------- Decision Variable U9zjt ---------------------------------------
//
//	for (z = 0; z<zmax; z++) {
//		IloNumVarMatrix2x2 U9jt(env, 0);
//		for (j = 0; j<jmax; j++) {
//			IloNumVarArray U9t(env, 0);
//			for (t = 0; t<tmax; t++) {
//				char Dual9[70];
//				sprintf(Dual9, "U9zjt(z%d,j%d,t%d)", z, j, t);
//				IloNumVar U9(env, 0, IloInfinity, ILOFLOAT, Dual9);
//				NoOfSlaveVars++;
//				U9t.add(U9);
//				AllVars.add(U9);
//			}
//			U9jt.add(U9t);
//		}
//		U9zjt.add(U9jt);
//	}
//
//	//-------------- Decision Variable U10zjt ---------------------------------------
//
//	for (z = 0; z<zmax; z++) {
//		IloNumVarMatrix2x2 U10jt(env, 0);
//		for (j = 0; j<jmax; j++) {
//			IloNumVarArray U10t(env, 0);
//			for (t = 0; t<tmax; t++) {
//				char Dual10[70];
//				sprintf(Dual10, "U10zjt(z%d,j%d,t%d)", z, j, t);
//				IloNumVar U10(env, 0, IloInfinity, ILOFLOAT, Dual10);
//				NoOfSlaveVars++;
//				U10t.add(U10);
//				AllVars.add(U10);
//			}
//			U10jt.add(U10t);
//		}
//		U10zjt.add(U10jt);
//	}
//
//	//-------------- Decision Variable U11izt ---------------------------------------
//
//	for (i = 0; i<imax; i++) {
//		IloNumVarMatrix2x2 U11zt(env, 0);
//		for (z = 0; z<zmax; z++) {
//			IloNumVarArray U11t(env, 0);
//			for (t = 0; t<tmax; t++) {
//				char Dual11[70];
//				sprintf(Dual11, "U11izt(i%d,z%d,t%d)", i, z, t);
//				IloNumVar U11(env, 0, IloInfinity, ILOFLOAT, Dual11);
//				NoOfSlaveVars++;
//				U11t.add(U11);
//				AllVars.add(U11);
//			}
//			U11zt.add(U11t);
//		}
//		U11izt.add(U11zt);
//	}
//
//	//-------------- Decision Variable U12kzt ---------------------------------------
//
//	for (k = 0; k<kmax; k++) {
//		IloNumVarMatrix2x2 U12zt(env, 0);
//		for (z = 0; z<zmax; z++) {
//			IloNumVarArray U12t(env, 0);
//			for (t = 0; t<tmax; t++) {
//				char Dual12[70];
//				sprintf(Dual12, "U12kzt(k%d,z%d,t%d)", k, z, t);
//				IloNumVar U12(env, 0, IloInfinity, ILOFLOAT, Dual12);
//				NoOfSlaveVars++;
//				U12t.add(U12);
//				AllVars.add(U12);
//			}
//			U12zt.add(U12t);
//		}
//		U12kzt.add(U12zt);
//	}
//
//	//-------------- Decision Variable U13izt ---------------------------------------
//
//	for (i = 0; i<imax; i++) {
//		IloNumVarMatrix2x2 U13zt(env, 0);
//		for (z = 0; z<zmax; z++) {
//			IloNumVarArray U13t(env, 0);
//			for (t = 0; t<tmax; t++) {
//				char Dual13[70];
//				sprintf(Dual13, "U13izt(i%d,z%d,t%d)", i, z, t);
//				IloNumVar U13(env, 0, IloInfinity, ILOFLOAT, Dual13);
//				NoOfSlaveVars++;
//				U13t.add(U13);
//				AllVars.add(U13);
//			}
//			U13zt.add(U13t);
//		}
//		U13izt.add(U13zt);
//	}
//
//	//-------------- Decision Variable U14kzt ---------------------------------------
//
//	for (k = 0; k<kmax; k++) {
//		IloNumVarMatrix2x2 U14zt(env, 0);
//		for (z = 0; z<zmax; z++) {
//			IloNumVarArray U14t(env, 0);
//			for (t = 0; t<tmax; t++) {
//				char Dual14[70];
//				sprintf(Dual14, "U14kzt(k%d,z%d,t%d)", k, z, t);
//				IloNumVar U14(env, 0, IloInfinity, ILOFLOAT, Dual14);
//				NoOfSlaveVars++;
//				U14t.add(U14);
//				AllVars.add(U14);
//			}
//			U14zt.add(U14t);
//		}
//		U14kzt.add(U14zt);
//	}
//
//
//	//----------------- END OF DECISION VARIABLES ------------------
//	//-----------------------------------------------------------------------------
//	//------------------------- Slave Dual Constraints ------------------------
//	//-----------------------------------------------------------------------------
//	//------------------------------ Con1Xizjt ------------------------------
//
//	for (i = 0; i<imax; i++) {
//		IloRangeMatrix3x3 Con1Xzjt(env, 0);
//		for (z = 0; z<zmax; z++) {
//			IloRangeMatrix2x2 Con1Xjt(env, 0);
//			for (j = 0; j<jmax; j++) {
//				IloRangeArray Con1Xt(env, 0);
//				for (t = 0; t<tmax; t++) {
//					IloExpr expr(env, 0);
//					expr += U1ijt[i][j][t] - U3zjt[z][j][t] - U5izt[i][z][t] + U6izt[i][z][t];
//					char Con1[60];
//					sprintf(Con1, "Con1Xizjt(i%d,z%d,j%d,t%d)", i, z, j, t);
//					double LBCon1Xizjt = -IloInfinity, UBCon1Xizjt = 0;
//					IloRange Con1X(env, LBCon1Xizjt, expr, UBCon1Xizjt, Con1);
//					NoOfSlaveCons++;
//					modelDualSlave.add(Con1X);
//					Con1Xt.add(Con1X);
//					expr.end();
//				}
//				Con1Xjt.add(Con1Xt);
//			}
//			Con1Xzjt.add(Con1Xjt);
//		}
//		Con1Xizjt.add(Con1Xzjt);
//	}
//
//	//------------------------------ Con2Yzkjt ------------------------------
//
//	for (z = 0; z<zmax; z++) {
//		IloRangeMatrix3x3 Con2Ykjt(env, 0);
//		for (k = 0; k<kmax; k++) {
//			IloRangeMatrix2x2 Con2Yjt(env, 0);
//			for (j = 0; j<jmax; j++) {
//				IloRangeArray Con2Yt(env, 0);
//				for (t = 0; t<tmax; t++) {
//					IloExpr expr(env, 0);
//					expr += U2kjt[k][j][t] + U3zjt[z][j][t] - U7kzt[k][z][t] + U8kzt[k][z][t];
//					char Con2[60];
//					sprintf(Con2, "Con2Yzkjt(z%d,k%d,j%d,t%d)", z, k, j, t);
//					double LBCon2Yzkjt = -IloInfinity, UBCon2Yzkjt = 0;
//					IloRange Con2Y(env, LBCon2Yzkjt, expr, UBCon2Yzkjt, Con2);
//					NoOfSlaveCons++;
//					modelDualSlave.add(Con2Y);
//					Con2Yt.add(Con2Y);
//					expr.end();
//				}
//				Con2Yjt.add(Con2Yt);
//			}
//			Con2Ykjt.add(Con2Yjt);
//		}
//		Con2Yzkjt.add(Con2Ykjt);
//	}
//
//
//	//------------------------------ Con3Izjt ------------------------------
//	for (z = 0; z<zmax; z++) {
//		IloRangeMatrix2x2 Con3Ijt(env, 0);
//		for (j = 0; j<jmax; j++) {
//			IloRangeArray Con3It(env, 0);
//			for (t = 0; t<tmax; t++) {
//				if (t<tmax - 1) {
//					IloExpr expr(env, 0);
//					expr += U3zjt[z][j][t] - U3zjt[z][j][t + 1] - U4zt[z][t] - U9zjt[z][j][t] + U10zjt[z][j][t];
//					char Con3[60];
//					sprintf(Con3, "Con3Izjt(z%d,j%d,t%d)", z, j, t);
//					double LBCon3Izjt = -IloInfinity, UBCon3Izjt = 0;
//					IloRange Con3I(env, LBCon3Izjt, expr, UBCon3Izjt, Con3);
//					NoOfSlaveCons++;
//					modelDualSlave.add(Con3I);
//					Con3It.add(Con3I);
//					expr.end();
//				}
//				else {
//					IloExpr expr(env, 0);
//					expr += U3zjt[z][j][t] - U4zt[z][t] - U9zjt[z][j][t] + U10zjt[z][j][t];
//					char Con3[60];
//					sprintf(Con3, "Con3Izjt(z%d,j%d,t%d)", z, j, t);
//					double LBCon3Izjt = -IloInfinity, UBCon3Izjt = 0;
//					IloRange Con3I(env, LBCon3Izjt, expr, UBCon3Izjt, Con3);
//					NoOfSlaveCons++;
//					modelDualSlave.add(Con3I);
//					Con3It.add(Con3I);
//					expr.end();
//				}
//			}
//			Con3Ijt.add(Con3It);
//		}
//		Con3Izjt.add(Con3Ijt);
//	}
//
//	//------------------------------ Con4SCizt ------------------------------
//
//	for (i = 0; i<imax; i++) {
//		IloRangeMatrix2x2 Con4SCzt(env, 0);
//		for (z = 0; z<zmax; z++) {
//			IloRangeArray Con4SCt(env, 0);
//			for (t = 0; t<tmax; t++) {
//				IloExpr expr(env, 0);
//				expr += -U11izt[i][z][t] + U13izt[i][z][t];
//				char Con4[60];
//				sprintf(Con4, "Con4SCizt(i%d,z%d,t%d)", i, z, t);
//				double LBCon4SCizt = -IloInfinity, UBCon4SCizt = 1;
//				IloRange Con4SC(env, LBCon4SCizt, expr, UBCon4SCizt, Con4);
//				NoOfSlaveCons++;
//				modelDualSlave.add(Con4SC);
//				Con4SCt.add(Con4SC);
//				expr.end();
//			}
//			Con4SCzt.add(Con4SCt);
//		}
//		Con4SCizt.add(Con4SCzt);
//	}
//
//	//------------------------------ Con5SDkzt ------------------------------
//
//	for (k = 0; k<kmax; k++) {
//		IloRangeMatrix2x2 Con5SDzt(env, 0);
//		for (z = 0; z<zmax; z++) {
//			IloRangeArray Con5SDt(env, 0);
//			for (t = 0; t<tmax; t++) {
//				IloExpr expr(env, 0);
//				expr += -U12kzt[k][z][t] + U14kzt[k][z][t];
//				char Con5[60];
//				sprintf(Con5, "Con5SDzkt(z%d,k%d,t%d)", z, k, t);
//				double LBCon5SDzkt = -IloInfinity, UBCon5SDzkt = 1;
//				IloRange Con5SD(env, LBCon5SDzkt, expr, UBCon5SDzkt, Con5);
//				NoOfSlaveCons++;
//				modelDualSlave.add(Con5SD);
//				Con5SDt.add(Con5SD);
//				expr.end();
//			}
//			Con5SDzt.add(Con5SDt);
//		}
//		Con5SDkzt.add(Con5SDzt);
//	}
//
//
//	//------------------------------------------------------------------------------
//	//------------------------------------------------------------------------------
//	//------------Objective Function of Dual Slave Problem--------------------------
//	//------------------------------------------------------------------------------
//
//	/*
//
//	IloExpr expr_slave(env);
//
//	for (i=0;i<imax;i++){
//	for (j=0;j<jmax;j++){
//	for (t=0;t<tmax;t++){
//	expr_slave+=E[i][t]*aeijt[i][j][t]*U1ijt[i][j][t];
//	}
//	}
//	}
//	for (k=0;k<kmax;k++){
//	for (j=0;j<jmax;j++){
//	for (t=0;t<tmax;t++){
//	expr_slave+=S[k][t]*askjt[k][j][t]*U2kjt[k][j][t];
//	}
//	}
//	}
//	for (z=0;z<zmax;z++){
//	for (j=0;j<jmax;j++){
//	//for (t=0;t<tmax;t++){
//	expr_slave+=initial[z][j]*U3zjt[z][j][0];
//	//}
//	}
//	}
//
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	expr_slave+=-Cap*U4zt[z][t];
//	}
//	}
//	for (i=0;i<imax;i++){
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	expr_slave+=-BigM*CiztValue[i][z][t]*U5izt[i][z][t];
//	}
//	}
//	}
//	for (i=0;i<imax;i++){
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	expr_slave+=CiztValue[i][z][t]*U6izt[i][z][t];
//	}
//	}
//	}
//	for (z=0;z<zmax;z++){
//	for (k=0;k<kmax;k++){
//	for (t=0;t<tmax;t++){
//	expr_slave+=-BigM*DzktValue[z][k][t]*U7kzt[z][k][t];
//	}
//	}
//	}
//	for (z=0;z<zmax;z++){
//	for (k=0;k<kmax;k++){
//	for (t=0;t<tmax;t++){
//	expr_slave+=DzktValue[z][k][t]*U8kzt[z][k][t];
//	}
//	}
//	}
//	for (z=0;z<zmax;z++){
//	for (j=0;j<jmax;j++){
//	for (t=0;t<tmax;t++){
//	expr_slave+=-BigM*FzjtValue[z][j][t]*U9zjt[z][j][t];
//	}
//	}
//	}
//	for (z=0;z<zmax;z++){
//	for (j=0;j<jmax;j++){
//	for (t=0;t<tmax;t++){
//	expr_slave+=FzjtValue[z][j][t]*U10zjt[z][j][t];
//	}
//	}
//	}
//	for (i=0;i<imax;i++){
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	expr_slave+=-CiztValue[i][z][t]*U11izt[i][z][t];
//	}
//	}
//	}
//	for (z=0;z<zmax;z++){
//	for (k=0;k<kmax;k++){
//	for (t=0;t<tmax;t++){
//	expr_slave+=-DzktValue[z][k][t]*U12kzt[z][k][t];
//	}
//	}
//	}
//	for (i=0;i<imax;i++){
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	if(t==0){
//	expr_slave+=CiztValue[i][z][t]*U13izt[i][z][t];
//	}else{
//	expr_slave+=(CiztValue[i][z][t]-CiztValue[i][z][t-1])*U13izt[i][z][t];
//	}
//	}
//	}
//	}
//	for (z=0;z<zmax;z++){
//	for (k=0;k<kmax;k++){
//	for (t=0;t<tmax;t++){
//	if(t==0){
//	expr_slave+=DzktValue[z][k][t]*U14kzt[z][k][t];
//	}else{
//	expr_slave+=(DzktValue[z][k][t]-DzktValue[z][k][t-1])*U14kzt[z][k][t];
//	}
//	}
//	}
//	}
//
//
//	modelDualSlave.add(IloMaximize(env, expr_slave));
//	expr_slave.end();
//	*/
//
//	Dual_objective = IloAdd(modelDualSlave, IloMaximize(env, 0));
//
//	return 0;
//}

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
			env.error() << "Failed to optimize Master Problem." << endl;
			env.out() << "----------------------------------------------------------------" << endl;
			*InfeasibleMaster = true;
			return 0;
		}
		int status_master = 0;

		//env.out() << "Solution status Master1 = " << cplexMaster_ptr.getStatus() << endl;
		//env.out() << "Solution value Master1= " << cplexMaster_ptr.getObjValue() << endl;
		status_master = cplexMaster_ptr.getStatus();
		//--------LOWER BOUND------------
		//if (status_master == 2) {
		UpperBound = cplexMaster_ptr.getObjValue();
		//}
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
//int UpdateDualSlaveObjective() {
//	int l = 0;
//	//---------------Update the objective function of the DUAL SLAVE problem---------------- 
//	for (i = 0; i<imax; i++) {
//		for (j = 0; j<jmax; j++) {
//			IloNumArray Dual_Obj_Coefs_U1(env, tmax);
//			l = 0;
//			for (t = 0; t<tmax; t++) {
//				Dual_Obj_Coefs_U1[l] = E[i][t] * ae[i][j][t];
//				l++;
//			}
//			Dual_objective.setLinearCoefs(U1ijt[i][j], Dual_Obj_Coefs_U1);
//		}
//	}
//	for (k = 0; k<kmax; k++) {
//		for (j = 0; j<jmax; j++) {
//			IloNumArray Dual_Obj_Coefs_U2(env, tmax);
//			l = 0;
//			for (t = 0; t<tmax; t++) {
//				Dual_Obj_Coefs_U2[l] = S[k][t] * as[k][j][t];
//				l++;
//			}
//			Dual_objective.setLinearCoefs(U2kjt[k][j], Dual_Obj_Coefs_U2);
//		}
//	}
//	for (z = 0; z<zmax; z++) {
//		for (j = 0; j<jmax; j++) {
//			IloNum Dual_Obj_Coefs_U3;
//			for (t = 0; t<1; t++) {
//				Dual_Obj_Coefs_U3 = initial[z][j];
//			}
//			Dual_objective.setLinearCoef(U3zjt[z][j][0], Dual_Obj_Coefs_U3);//setLinearCoefs(U3zjt[z][j],Dual_Obj_Coefs_U3);
//		}
//	}
//	for (z = 0; z<zmax; z++) {
//		IloNumArray Dual_Obj_Coefs_U4(env, tmax);
//		l = 0;
//		for (t = 0; t<tmax; t++) {
//			Dual_Obj_Coefs_U4[l] = -capmax;
//			l++;
//		}
//		Dual_objective.setLinearCoefs(U4zt[z], Dual_Obj_Coefs_U4);
//	}
//	for (i = 0; i<imax; i++) {
//		for (z = 0; z<zmax; z++) {
//			IloNumArray Dual_Obj_Coefs_U5(env, tmax);
//			l = 0;
//			for (t = 0; t<tmax; t++) {
//				Dual_Obj_Coefs_U5[l] = -BigM * CiztValue[i][z][t];
//				l++;
//			}
//			Dual_objective.setLinearCoefs(U5izt[i][z], Dual_Obj_Coefs_U5);
//		}
//	}
//
//	for (i = 0; i<imax; i++) {
//		for (z = 0; z<zmax; z++) {
//			IloNumArray Dual_Obj_Coefs_U6(env, tmax);
//			l = 0;
//			for (t = 0; t<tmax; t++) {
//				Dual_Obj_Coefs_U6[l] = CiztValue[i][z][t];
//				l++;
//			}
//			Dual_objective.setLinearCoefs(U6izt[i][z], Dual_Obj_Coefs_U6);
//		}
//	}
//
//	for (k = 0; k<kmax; k++) {
//		for (z = 0; z<zmax; z++) {
//			IloNumArray Dual_Obj_Coefs_U7(env, tmax);
//			l = 0;
//			for (t = 0; t<tmax; t++) {
//				Dual_Obj_Coefs_U7[l] = -BigM * DkztValue[k][z][t];
//				l++;
//			}
//			Dual_objective.setLinearCoefs(U7kzt[k][z], Dual_Obj_Coefs_U7);
//		}
//	}
//
//	for (k = 0; k<kmax; k++) {
//		for (z = 0; z<zmax; z++) {
//			IloNumArray Dual_Obj_Coefs_U8(env, tmax);
//			l = 0;
//			for (t = 0; t<tmax; t++) {
//				Dual_Obj_Coefs_U8[l] = DkztValue[k][z][t];
//				l++;
//			}
//			Dual_objective.setLinearCoefs(U8kzt[k][z], Dual_Obj_Coefs_U8);
//		}
//	}
//
//	for (z = 0; z<zmax; z++) {
//		for (j = 0; j<jmax; j++) {
//			IloNumArray Dual_Obj_Coefs_U9(env, tmax);
//			l = 0;
//			for (t = 0; t<tmax; t++) {
//				Dual_Obj_Coefs_U9[l] = -BigM * FzjtValue[z][j][t];
//				l++;
//			}
//			Dual_objective.setLinearCoefs(U9zjt[z][j], Dual_Obj_Coefs_U9);
//		}
//	}
//
//	for (z = 0; z<zmax; z++) {
//		for (j = 0; j<jmax; j++) {
//			IloNumArray Dual_Obj_Coefs_U10(env, tmax);
//			l = 0;
//			for (t = 0; t<tmax; t++) {
//				Dual_Obj_Coefs_U10[l] = FzjtValue[z][j][t];
//				l++;
//			}
//			Dual_objective.setLinearCoefs(U10zjt[z][j], Dual_Obj_Coefs_U10);
//		}
//	}
//	for (i = 0; i<imax; i++) {
//		for (z = 0; z<zmax; z++) {
//			IloNumArray Dual_Obj_Coefs_U11(env, tmax);
//			l = 0;
//			for (t = 0; t<tmax; t++) {
//				Dual_Obj_Coefs_U11[l] = -CiztValue[i][z][t];
//				l++;
//			}
//			Dual_objective.setLinearCoefs(U11izt[i][z], Dual_Obj_Coefs_U11);
//		}
//	}
//
//	for (k = 0; k<kmax; k++) {
//		for (z = 0; z<zmax; z++) {
//			IloNumArray Dual_Obj_Coefs_U12(env, tmax);
//			l = 0;
//			for (t = 0; t<tmax; t++) {
//				Dual_Obj_Coefs_U12[l] = -DkztValue[k][z][t];
//				l++;
//			}
//			Dual_objective.setLinearCoefs(U12kzt[k][z], Dual_Obj_Coefs_U12);
//		}
//	}
//	for (i = 0; i<imax; i++) {
//		for (z = 0; z<zmax; z++) {
//			IloNumArray Dual_Obj_Coefs_U13(env, tmax);
//			l = 0;
//			for (t = 0; t<tmax; t++) {
//				if (t == 0) {
//					Dual_Obj_Coefs_U13[l] = CiztValue[i][z][t];
//					l++;
//				}
//				else {
//					Dual_Obj_Coefs_U13[l] = (CiztValue[i][z][t] - CiztValue[i][z][t - 1]);
//					l++;
//				}
//			}
//			Dual_objective.setLinearCoefs(U13izt[i][z], Dual_Obj_Coefs_U13);
//		}
//	}
//
//
//	for (k = 0; k<kmax; k++) {
//		for (z = 0; z<zmax; z++) {
//			IloNumArray Dual_Obj_Coefs_U14(env, tmax);
//			l = 0;
//			for (t = 0; t<tmax; t++) {
//				if (t == 0) {
//					Dual_Obj_Coefs_U14[l] = DkztValue[k][z][t];
//					l++;
//				}
//				else {
//					Dual_Obj_Coefs_U14[l] = (DkztValue[k][z][t] - DkztValue[k][z][t - 1]);
//					l++;
//				}
//			}
//			Dual_objective.setLinearCoefs(U14kzt[k][z], Dual_Obj_Coefs_U14);
//		}
//	}
//
//
//	return 0;
//}
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

int Solve_Dual_Slave(int i_ptr) {

	int stop = 0;
	int status = 1;
	int j_bar = 0;
	int  k = 0;
	double min_Dis = 0;
	int CountNear_v_vehs = 0;

	for (j = 0; j < jmax; j++) { // jmax equals to the number of potential facility points(49, …)
		if (X_vjValue[j] > 0.01 && Distance_ij[i_ptr][j] <= v_standard) {
			CountNear_v_vehs++;
		}
	}



	/*Lamda1_iValue[i_ptr] = 0;
	Lamda2_iValue[i_ptr] = 0;
	for (j = 0; j < jmax; j++) {
		Beta_ijValue[i_ptr][j] = 0;
		Gamma_ijValue[i_ptr][j] = 0;
		Y_vijValue[i_ptr][j] = 0;
		Y_mijValue[i_ptr][j] = 0;
	}*/




	for (j = 0; j < jmax; j++) { // jmax equals to the number of potential facility points(49, …)
		if (X_vjValue[j] > 0.01 && Distance_ij[i_ptr][j] <= v_standard) {
			if (CountNear_v_vehs == 1) {

				Lamda1_iValue[i_ptr] = 0;
				Lamda2_iValue[i_ptr] = 0;
				for (k = 0; k < jmax; k++) {
					if (Distance_ij[k][j] + Distance_ij[i_ptr][j] <= v_standard || Distance_ij[i_ptr][k] <= v_standard) {//  
						Beta_ijValue[i_ptr][k] = Importance_i[i_ptr];
						//Beta_ijValue[k][i_ptr] = Importance_i[k];
					}
					else {
						Beta_ijValue[i_ptr][k] = 0;
					}
					//Beta_ijValue[i_ptr][k] = 0; //A jmax by 1 vector whose elements are all zero.
					Gamma_ijValue[i_ptr][k] = 0;
					Y_vijValue[i_ptr][k] = 0;
					Y_mijValue[i_ptr][k] = 0;
				}
			}
			else {
				Lamda1_iValue[i_ptr] = 0;
				Lamda2_iValue[i_ptr] = Importance_i[i_ptr];
				for (k = 0; k < jmax; k++) {
					Beta_ijValue[i_ptr][k] = 0;
					Gamma_ijValue[i_ptr][k] = 0;
					Y_vijValue[i_ptr][k] = 0;
					Y_mijValue[i_ptr][k] = 0;
				}
			}
			Y_vijValue[i_ptr][j] = 1;
			stop = 1;
			j = jmax;
		}
	}

	if (stop == 0) {
		for (j = 0; j < jmax; j++) {
			if (X_mjValue[j] > 0.01 && Distance_ij[i_ptr][j] <= m_standard) {
				min_Dis = Big_M;
				j_bar = 0;
				for (k = 0; k < jmax; k++) {
					if (X_vjValue[k] > 0.01 && Distance_ij[i_ptr][k] < min_Dis) {
						min_Dis = Distance_ij[i_ptr][k];
						j_bar = k;
					}
				}
				Lamda1_iValue[i_ptr] = -Weight * Importance_i[i_ptr] * Distance_ij[i_ptr][j_bar];
				Lamda2_iValue[i_ptr] = 0;
				for (k = 0; k < jmax; k++) {
					Gamma_ijValue[i_ptr][k] = 0;
					Y_vijValue[i_ptr][k] = 0;
					Y_mijValue[i_ptr][k] = 0;
					if (Distance_ij[i_ptr][k] <= v_standard) {
						Beta_ijValue[i_ptr][k] = Importance_i[i_ptr] + Weight * Importance_i[i_ptr] * Distance_ij[i_ptr][j_bar];
					}
					else {
						Beta_ijValue[i_ptr][k] = -Weight * Importance_i[i_ptr] * Distance_ij[i_ptr][k] + Weight * Importance_i[i_ptr] * Distance_ij[i_ptr][j_bar];
						if (Beta_ijValue[i_ptr][k] < 0) {
							Beta_ijValue[i_ptr][k] = 0;
						}
					}
				}
				Y_vijValue[i_ptr][j_bar] = 1;
				Y_mijValue[i_ptr][j] = 1;
				/*for (k = 0; k < jmax; k++) {
				if (X_mjValue[j] == 1 && Distance_ij[i_ptr][k] <= m_standard) {

				}
				}*/
				stop = 1;
				j = jmax;
			}
		}
		if (stop == 0) {
			status = 0; //i.e.DSP_i is unbounded
			Lamda1_iValue[i_ptr] = 0;
			Lamda2_iValue[i_ptr] = -1;
			for (k = 0; k < jmax; k++) {
				Beta_ijValue[i_ptr][k] = 0;
				Gamma_ijValue[i_ptr][k] = 0;
				if (Distance_ij[i_ptr][k] <= v_standard) {
					Beta_ijValue[i_ptr][k] = 1;
				}
				if (Distance_ij[i_ptr][k] <= m_standard) {
					Gamma_ijValue[i_ptr][k] = 1;
				}
			}
		}
	}
	status_dual[i_ptr] = status;//A vector of imax elements with the status of i-th solution
	return 0;
}
int Dual_Slave_Unbounded(IloEnv env) {
	//env.error() << "Dual Slave Problem is UNBOUNDED" << endl;
	//env.out() << "----------------------------------------------------------------" << endl;
	//------Lower Bound Global remains the same--------
	LowerBound = -Big_M;
	LowerBoundGlobal = LowerBoundGlobal;

	cTx.push_back(0);
	bTu.push_back(-Big_M);
	return 0;
}
int Dual_Slave_Bounded(IloEnv env, double* DTransposeY, double* DualSlaveObjFunction, double* PrimalSlaveObjFunction) {
	//env.error() << "Dual Slave Problem is BOUNDED" << endl;
	//env.error() << "Found a FEASIBLE solution of Slave LP" << endl;
	//env.out() << "----------------------------------------------------------------" << endl;
	*DualSlaveObjFunction = 0;
	for (i = 0; i < imax; i++) {
		for (j = 0; j < jmax; j++) {
			*DualSlaveObjFunction = *DualSlaveObjFunction + X_vjValue[j] * Beta_ijValue[i][j] + X_mjValue[j] * Gamma_ijValue[i][j];
		}
		*DualSlaveObjFunction = *DualSlaveObjFunction + Lamda1_iValue[i] + Lamda2_iValue[i];
	}

	*PrimalSlaveObjFunction = *DualSlaveObjFunction;
	LowerBound = *DualSlaveObjFunction;


	if (LowerBound < LowerBoundGlobal) {//-----We found a worse feasible solution---
		LowerBoundGlobal = LowerBoundGlobal;
	}
	else {//-----------We found a better feasible solution-------
		LowerBoundGlobal = LowerBound;//Update Upper Bound
		OptimalOriginalObjFunction = LowerBoundGlobal;
		OptimalMasterObjFunction = *DTransposeY + ThetaValue;
		OptimalPrimalSlaveObjFunction = *PrimalSlaveObjFunction;
		OptimalDualSlaveObjFunction = *DualSlaveObjFunction;
		OptimalObjFunctionFirstTerm = 0;
		OptimalObjFunctionSecondTerm = 0;
		for (j = 0; j < jmax; j++) {
			OptimalX_vjValue[j] = X_vjValue[j];
			OptimalX_mjValue[j] = X_mjValue[j];
		}
		for (i = 0; i < imax; i++) {
			for (j = 0; j < jmax; j++) {
				OptimalY_vijValue[i][j] = Y_vijValue[i][j];
				OptimalY_mijValue[i][j] = Y_mijValue[i][j];
				OptimalObjFunctionFirstTerm = OptimalObjFunctionFirstTerm + Importance_i[i] * Cv_ij[i][j] * OptimalY_vijValue[i][j];
				OptimalObjFunctionSecondTerm = OptimalObjFunctionSecondTerm - Weight * Importance_i[i] * (1 - Cv_ij[i][j]) * Distance_ij[i][j] * OptimalY_vijValue[i][j];
				OptimalBeta_ijValue[i][j] = Beta_ijValue[i][j];
				OptimalGamma_ijValue[i][j] = Gamma_ijValue[i][j];
			}
			OptimalLamda1_iValue[i] = Lamda1_iValue[i];
			OptimalLamda2_iValue[i] = Lamda2_iValue[i];
		}

		OptimalThetaValue = ThetaValue;

	}//end of else (better feasible solution found)
	//cout << "OptimalObjFunctionFirstTerm=" << OptimalObjFunctionFirstTerm << endl;
	//cout << "OptimalObjFunctionSecondTerm=" << OptimalObjFunctionSecondTerm << endl;
	//cout << "PercentOfSecondTerm=" << abs(OptimalObjFunctionSecondTerm) / (OptimalObjFunctionFirstTerm + OptimalObjFunctionSecondTerm) << endl;

	cTx.push_back(*PrimalSlaveObjFunction);
	bTu.push_back(*DualSlaveObjFunction);


	return 0;
}
//int GetExtremeRayOfDSP(IloCplex cplexDualSlave_ptr) {
//	//----------------Get an extreme ray of the DUAL SLAVE problem-------------
//	//cout<<"size of Array ="<<FeasvalsDualRangeSumXijt.getSize()<<endl;
//
//	//cplexSlave_ptr.dualFarkas(SumXijt[0][0],FeasvalsDualRangeSumXijt);
//	//cout<<"size of Array ="<<FeasvalsDualRangeSumXijt.getSize()<<endl;
//	/*
//	for (l=0;l<FeasvalsDualRangeSumXijt.getSize();l++){
//	if(FeasvalsDualRangeSumXijt[l]!=0){
//	cout<<"FeasvalsDualRangeSumXijt["<<l<<"]="<<FeasvalsDualRangeSumXijt[l]<<endl;
//	}
//	}
//	*/
//
//
//	//IloExpr ray=cplexDualSlave_ptr.getRay();
//	//System.out.println("getRay returned " + ray.toString());
//
//
//	for (t = 0; t<tmax; t++) {
//		for (j = 0; j<jmax; j++) {
//			for (i = 0; i<imax; i++) {
//				U1Valueijt[i][j][t] = 0;
//			}
//			for (k = 0; k<kmax; k++) {
//				U2Valuekjt[k][j][t] = 0;
//			}
//			for (z = 0; z<zmax; z++) {
//				U3Valuezjt[z][j][t] = 0;
//				U9Valuezjt[z][j][t] = 0;
//				U10Valuezjt[z][j][t] = 0;
//			}
//		}
//		for (z = 0; z<zmax; z++) {
//			U4Valuezt[z][t] = 0;
//			for (i = 0; i<imax; i++) {
//				U5Valueizt[i][z][t] = 0;
//				U6Valueizt[i][z][t] = 0;
//				U11Valueizt[i][z][t] = 0;
//				U13Valueizt[i][z][t] = 0;
//			}
//			for (k = 0; k<kmax; k++) {
//				U7Valuekzt[k][z][t] = 0;
//				U8Valuekzt[k][z][t] = 0;
//				U12Valuekzt[k][z][t] = 0;
//				U14Valuekzt[k][z][t] = 0;
//			}
//		}
//	}
//
//
//	cout << "size of variables =" << AllVars.getSize() << endl;
//	cout << "size of Array =" << U1NumValueijt.getSize() << endl;
//	cplexDualSlave_ptr.getRay(U1NumValueijt, AllVars);
//
//	cout << "size of Array =" << U1NumValueijt.getSize() << endl;
//	cout << "size of variables =" << AllVars.getSize() << endl;
//
//	//IloNumExpr rayantonis;
//	//cplexDualSlave_ptr.getRay(rayantonis,U1ijt[0][0]);
//	for (l = 0; l<U1NumValueijt.getSize(); l++) {
//		if (U1NumValueijt[l] != 0) {
//			//cout<<"U1NumValueijt["<<l<<"]="<<U1NumValueijt[l]<<endl;
//		}
//	}
//
//	//sprintf(Dual1,"U1ijt(i%d,j%d,t%d)",i,j,t);
//	//for ( l = 0; l < U1NumValueijt.getSize(); ++l){
//	//cout << l << ", " << U1NumValueijt[l] << " [" << U1ijt[l].getImpl() << "]"<<endl;
//
//	//}
//
//	for (i = 0; i<imax; i++) {
//		for (j = 0; j<jmax; j++) {
//			for (t = 0; t<tmax; t++) {
//				for (l = 0; l<U1NumValueijt.getSize(); l++) {
//					if (AllVars[l].getId() == U1ijt[i][j][t].getId()) {
//						U1Valueijt[i][j][t] = U1NumValueijt[l];
//						//cout<<"U1Valueijt["<<i<<"]["<<j<<"]["<<t<<"] ="<<U1Valueijt[i][j][t]<<endl;
//					}
//					else {
//						//U1Valueijt[i][j][t]=0;
//					}
//				}
//			}
//		}
//	}
//	for (k = 0; k<kmax; k++) {
//		for (j = 0; j<jmax; j++) {
//			for (t = 0; t<tmax; t++) {
//				for (l = 0; l<U1NumValueijt.getSize(); l++) {
//					if (AllVars[l].getId() == U2kjt[k][j][t].getId()) {
//						U2Valuekjt[k][j][t] = U1NumValueijt[l];
//						//cout<<"U2Valuekjt["<<k<<"]["<<j<<"]["<<t<<"] ="<<U2Valuekjt[k][j][t]<<endl;
//					}
//					else {
//						//U2Valuekjt[k][j][t]=0;
//					}
//				}
//			}
//		}
//	}
//	for (z = 0; z<zmax; z++) {
//		for (j = 0; j<jmax; j++) {
//			for (t = 0; t<tmax; t++) {
//				for (l = 0; l<U1NumValueijt.getSize(); l++) {
//					if (AllVars[l].getId() == U3zjt[z][j][t].getId()) {
//						U3Valuezjt[z][j][t] = U1NumValueijt[l];
//						//cout<<"U3Valuezjt["<<z<<"]["<<j<<"]["<<t<<"] ="<<U3Valuezjt[z][j][t]<<endl;
//					}
//					else {
//						//U3Valuezjt[z][j][t]=0;
//					}
//				}
//			}
//		}
//	}
//	for (z = 0; z<zmax; z++) {
//		for (t = 0; t<tmax; t++) {
//			for (l = 0; l<U1NumValueijt.getSize(); l++) {
//				if (AllVars[l].getId() == U4zt[z][t].getId()) {
//					U4Valuezt[z][t] = U1NumValueijt[l];
//					//cout<<"U4Valuezt["<<z<<"]["<<t<<"] ="<<U4Valuezt[z][t]<<endl;
//				}
//				else {
//					//U4Valuezt[z][t]=0;
//				}
//			}
//		}
//	}
//
//	for (i = 0; i<imax; i++) {
//		for (z = 0; z<zmax; z++) {
//			for (t = 0; t<tmax; t++) {
//				for (l = 0; l<U1NumValueijt.getSize(); l++) {
//					if (AllVars[l].getId() == U5izt[i][z][t].getId()) {
//						U5Valueizt[i][z][t] = U1NumValueijt[l];
//						//cout<<"U5Valueizt["<<i<<"]["<<z<<"]["<<t<<"] ="<<U5Valueizt[i][z][t]<<endl;
//					}
//					else {
//						//U5Valueizt[i][z][t]=0;
//					}
//				}
//			}
//		}
//	}
//	for (i = 0; i<imax; i++) {
//		for (z = 0; z<zmax; z++) {
//			for (t = 0; t<tmax; t++) {
//				for (l = 0; l<U1NumValueijt.getSize(); l++) {
//					if (AllVars[l].getId() == U6izt[i][z][t].getId()) {
//						U6Valueizt[i][z][t] = U1NumValueijt[l];
//						//cout<<"U6Valueizt["<<i<<"]["<<z<<"]["<<t<<"] ="<<U6Valueizt[i][z][t]<<endl;
//					}
//					else {
//						//U6Valueizt[i][z][t]=0;
//					}
//				}
//			}
//		}
//	}
//	for (k = 0; k<kmax; k++) {
//		for (z = 0; z<zmax; z++) {
//			for (t = 0; t<tmax; t++) {
//				for (l = 0; l<U1NumValueijt.getSize(); l++) {
//					if (AllVars[l].getId() == U7kzt[k][z][t].getId()) {
//						U7Valuekzt[k][z][t] = U1NumValueijt[l];
//						//cout<<"U7Valuekzt["<<k<<"]["<<z<<"]["<<t<<"] ="<<U7Valuekzt[k][z][t]<<endl;
//					}
//					else {
//						//U7Valuekzt[k][z][t]=0;
//					}
//				}
//			}
//		}
//	}
//	for (k = 0; k<kmax; k++) {
//		for (z = 0; z<zmax; z++) {
//			for (t = 0; t<tmax; t++) {
//				for (l = 0; l<U1NumValueijt.getSize(); l++) {
//					if (AllVars[l].getId() == U8kzt[k][z][t].getId()) {
//						U8Valuekzt[k][z][t] = U1NumValueijt[l];
//						//cout<<"U8Valuekzt["<<k<<"]["<<z<<"]["<<t<<"] ="<<U8Valuekzt[k][z][t]<<endl;
//					}
//					else {
//						//U8Valuekzt[k][z][t]=0;
//					}
//				}
//			}
//		}
//	}
//
//	for (z = 0; z<zmax; z++) {
//		for (j = 0; j<jmax; j++) {
//			for (t = 0; t<tmax; t++) {
//				for (l = 0; l<U1NumValueijt.getSize(); l++) {
//					if (AllVars[l].getId() == U9zjt[z][j][t].getId()) {
//						U9Valuezjt[z][j][t] = U1NumValueijt[l];
//						//cout<<"U9Valuezjt["<<z<<"]["<<j<<"]["<<t<<"] ="<<U9Valuezjt[z][j][t]<<endl;
//					}
//					else {
//						//U9Valuezjt[z][j][t]=0;
//					}
//				}
//			}
//		}
//	}
//	for (z = 0; z<zmax; z++) {
//		for (j = 0; j<jmax; j++) {
//			for (t = 0; t<tmax; t++) {
//				for (l = 0; l<U1NumValueijt.getSize(); l++) {
//					if (AllVars[l].getId() == U10zjt[z][j][t].getId()) {
//						U10Valuezjt[z][j][t] = U1NumValueijt[l];
//						//cout<<"U10Valuezjt["<<z<<"]["<<j<<"]["<<t<<"] ="<<U10Valuezjt[z][j][t]<<endl;
//					}
//					else {
//						//U10Valuezjt[z][j][t]=0;
//					}
//				}
//			}
//		}
//	}
//	for (i = 0; i<imax; i++) {
//		for (z = 0; z<zmax; z++) {
//			for (t = 0; t<tmax; t++) {
//				for (l = 0; l<U1NumValueijt.getSize(); l++) {
//					if (AllVars[l].getId() == U11izt[i][z][t].getId()) {
//						U11Valueizt[i][z][t] = U1NumValueijt[l];
//						//cout<<"U11Valueizt["<<i<<"]["<<z<<"]["<<t<<"] ="<<U11Valueizt[i][z][t]<<endl;
//					}
//					else {
//						//U11Valueizt[i][z][t]=0;
//					}
//				}
//			}
//		}
//	}
//	for (k = 0; k<kmax; k++) {
//		for (z = 0; z<zmax; z++) {
//			for (t = 0; t<tmax; t++) {
//				for (l = 0; l<U1NumValueijt.getSize(); l++) {
//					if (AllVars[l].getId() == U12kzt[k][z][t].getId()) {
//						U12Valuekzt[k][z][t] = U1NumValueijt[l];
//						//cout<<"U12Valuekzt["<<k<<"]["<<z<<"]["<<t<<"] ="<<U12Valuekzt[k][z][t]<<endl;
//					}
//					else {
//						//U12Valuekzt[k][z][t]=0;
//					}
//				}
//			}
//		}
//	}
//	for (i = 0; i<imax; i++) {
//		for (z = 0; z<zmax; z++) {
//			for (t = 0; t<tmax; t++) {
//				for (l = 0; l<U1NumValueijt.getSize(); l++) {
//					if (AllVars[l].getId() == U13izt[i][z][t].getId()) {
//						U13Valueizt[i][z][t] = U1NumValueijt[l];
//						//cout<<"U13Valueizt["<<i<<"]["<<z<<"]["<<t<<"] ="<<U13Valueizt[i][z][t]<<endl;
//					}
//					else {
//						//U13Valueizt[i][z][t]=0;
//					}
//				}
//			}
//		}
//	}
//
//	for (k = 0; k<kmax; k++) {
//		for (z = 0; z<zmax; z++) {
//			for (t = 0; t<tmax; t++) {
//				for (l = 0; l<U1NumValueijt.getSize(); l++) {
//					if (AllVars[l].getId() == U14kzt[k][z][t].getId()) {
//						U14Valuekzt[k][z][t] = U1NumValueijt[l];
//						//cout<<"U14Valuekzt["<<k<<"]["<<z<<"]["<<t<<"] ="<<U14Valuekzt[k][z][t]<<endl;
//					}
//					else {
//						//U14Valuekzt[k][z][t]=0;
//					}
//				}
//			}
//		}
//	}
//
//
//	/*
//	for (i=0;i<imax;i++){
//	for (j=0;j<jmax;j++){
//	cout<<"size of Array ="<<U1NumValueijt.getSize()<<endl;
//	cplexDualSlave_ptr.getRay(U1NumValueijt,U1ijt[i][j]);
//	cout<<"size of Array ="<<U1NumValueijt.getSize()<<endl;
//	l=0;
//	for (t=0;t<tmax;t++){
//	U1Valueijt[i][j][t]=U1NumValueijt[l];
//	l++;
//	}
//	}
//	}
//
//
//	for (k=0;k<kmax;k++){
//	for (j=0;j<jmax;j++){
//	cout<<"size of Array ="<<U2NumValuekjt.getSize()<<endl;
//	cplexDualSlave_ptr.getRay(U2NumValuekjt,U2kjt[k][j]);
//	cout<<"size of Array ="<<U2NumValuekjt.getSize()<<endl;
//	l=0;
//	for (t=0;t<tmax;t++){
//	U2Valuekjt[k][j][t]=U2NumValuekjt[l];
//	l++;
//	}
//	}
//	}
//	for(z=0;z<zmax;z++){
//	for (j=0;j<jmax;j++){
//	cout<<"size of Array ="<<U3NumValuezjt.getSize()<<endl;
//	cplexDualSlave_ptr.getRay(U3NumValuezjt,U3zjt[z][j]);
//	cout<<"size of Array ="<<U3NumValuezjt.getSize()<<endl;
//	l=0;
//	for (t=0;t<tmax;t++){
//	U3Valuezjt[z][j][t]=U3NumValuezjt[l];
//	l++;
//	}
//	}
//	}
//	for(z=0;z<zmax;z++){
//	for (j=0;j<jmax;j++){
//	cplexDualSlave_ptr.getRay(U9NumValuezjt,U9zjt[z][j]);
//	l=0;
//	for (t=0;t<tmax;t++){
//	U9Valuezjt[z][j][t]=U9NumValuezjt[l];
//	l++;
//	}
//	}
//	}
//	for(z=0;z<zmax;z++){
//	for (j=0;j<jmax;j++){
//	cplexDualSlave_ptr.getRay(U10NumValuezjt,U10zjt[z][j]);
//	l=0;
//	for (t=0;t<tmax;t++){
//	U10Valuezjt[z][j][t]=U10NumValuezjt[l];
//	l++;
//	}
//	}
//	}
//
//	for(z=0;z<zmax;z++){
//	cplexDualSlave_ptr.getRay(U4NumValuezt,U4zt[z]);
//	l=0;
//	for (t=0;t<tmax;t++){
//	U4Valuezt[z][t]=U4NumValuezt[l];
//	l++;
//	}
//	}
//	for (i=0;i<imax;i++){
//	for(z=0;z<zmax;z++){
//	cplexDualSlave_ptr.getRay(U5NumValueizt,U5izt[i][z]);
//	l=0;
//	for (t=0;t<tmax;t++){
//	U5Valueizt[i][z][t]=U5NumValueizt[l];
//	l++;
//	}
//	}
//	}
//	for (i=0;i<imax;i++){
//	for(z=0;z<zmax;z++){
//	cplexDualSlave_ptr.getRay(U6NumValueizt,U6izt[i][z]);
//	l=0;
//	for (t=0;t<tmax;t++){
//	U6Valueizt[i][z][t]=U6NumValueizt[l];
//	l++;
//	}
//	}
//	}
//	for (i=0;i<imax;i++){
//	for(z=0;z<zmax;z++){
//	cplexDualSlave_ptr.getRay(U11NumValueizt,U11izt[i][z]);
//	l=0;
//	for (t=0;t<tmax;t++){
//	U11Valueizt[i][z][t]=U11NumValueizt[l];
//	l++;
//	}
//	}
//	}
//
//	for (i=0;i<imax;i++){
//	for(z=0;z<zmax;z++){
//	cplexDualSlave_ptr.getRay(U13NumValueizt,U13izt[i][z]);
//	l=0;
//	for (t=0;t<tmax;t++){
//	U13Valueizt[i][z][t]=U13NumValueizt[l];
//	l++;
//	}
//	}
//	}
//
//	for (k=0;k<kmax;k++){
//	for(z=0;z<zmax;z++){
//	cplexDualSlave_ptr.getRay(U7NumValuekzt,U7kzt[k][z]);
//	l=0;
//	for (t=0;t<tmax;t++){
//	U7Valuekzt[k][z][t]=U7NumValuekzt[l];
//	l++;
//	}
//	}
//	}
//	for (k=0;k<kmax;k++){
//	for(z=0;z<zmax;z++){
//	cplexDualSlave_ptr.getRay(U8NumValuekzt,U8kzt[k][z]);
//	l=0;
//	for (t=0;t<tmax;t++){
//	U8Valuekzt[k][z][t]=U8NumValuekzt[l];
//	l++;
//	}
//	}
//	}
//	for (k=0;k<kmax;k++){
//	for(z=0;z<zmax;z++){
//	cplexDualSlave_ptr.getRay(U12NumValuekzt,U12kzt[k][z]);
//	l=0;
//	for (t=0;t<tmax;t++){
//	U12Valuekzt[k][z][t]=U12NumValuekzt[l];
//	l++;
//	}
//	}
//	}
//	for (k=0;k<kmax;k++){
//	for(z=0;z<zmax;z++){
//	cplexDualSlave_ptr.getRay(U14NumValuekzt,U14kzt[k][z]);
//	l=0;
//	for (t=0;t<tmax;t++){
//	U14Valuekzt[k][z][t]=U14NumValuekzt[l];
//	l++;
//	}
//	}
//	}
//	*/
//
//
//
//	/*
//	l=0;
//	for (i=0;i<imax;i++){
//	for (j=0;j<jmax;j++){
//	for (t=0;t<tmax;t++){
//	S2valsDualSumXijt[i][j][t]=FeasvalsDualRangeSumXijt[l];
//	l++;
//	}
//	}
//	}
//	for (i=0;i<imax;i++){
//	for (j=0;j<jmax;j++){
//	for (t=0;t<tmax;t++){
//	S22valsDualSumXijt[i][j][t]=FeasvalsDualRangeSumXijt[l];
//	l++;
//	}
//	}
//	}
//
//	for (k=0;k<kmax;k++){
//	for (j=0;j<jmax;j++){
//	for (t=0;t<tmax;t++){
//	S2valsDualSumYkjt[k][j][t]=FeasvalsDualRangeSumXijt[l];
//	l++;
//	}
//	}
//	}
//	for (k=0;k<kmax;k++){
//	for (j=0;j<jmax;j++){
//	for (t=0;t<tmax;t++){
//	S22valsDualSumYkjt[k][j][t]=FeasvalsDualRangeSumXijt[l];
//	l++;
//	}
//	}
//	}
//
//	for (z=0;z<zmax;z++){
//	for (j=0;j<jmax;j++){
//	for (t=0;t<tmax;t++){
//	S2valsDualCTIzjt[z][j][t]=FeasvalsDualRangeSumXijt[l];
//	l++;
//	}
//	}
//	}
//
//	for (z=0;z<zmax;z++){
//	for (j=0;j<jmax;j++){
//	for (t=0;t<tmax;t++){
//	S22valsDualCTIzjt[z][j][t]=FeasvalsDualRangeSumXijt[l];
//	l++;
//	}
//	}
//	}
//
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	S2valsDualSum_Izt[z][t]=FeasvalsDualRangeSumXijt[l];
//	l++;
//	}
//	}
//
//	for (i=0;i<imax;i++){
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	S2valsDualCT1Fonctionement_Cizt[i][z][t]=FeasvalsDualRangeSumXijt[l];
//	l++;
//	}
//	}
//	}
//
//	for (i=0;i<imax;i++){
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	S2valsDualCT2Fonctionement_Cizt[i][z][t]=FeasvalsDualRangeSumXijt[l];
//	l++;
//	}
//	}
//	}
//
//	for (k=0;k<kmax;k++){
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	S2valsDualCT1Fonctionement_Dkzt[k][z][t]=FeasvalsDualRangeSumXijt[l];
//	l++;
//	}
//	}
//	}
//
//	for (k=0;k<kmax;k++){
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	S2valsDualCT2Fonctionement_Dkzt[k][z][t]=FeasvalsDualRangeSumXijt[l];
//	l++;
//	}
//	}
//	}
//
//
//	for (z=0;z<zmax;z++){
//	for(j=0;j<jmax;j++){
//	for (t=0;t<tmax;t++){
//	S2valsDualCT1Melzjt[z][j][t]=FeasvalsDualRangeSumXijt[l];
//	l++;
//	}
//	}
//	}
//
//	for (z=0;z<zmax;z++){
//	for(j=0;j<jmax;j++){
//	for (t=0;t<tmax;t++){
//	S2valsDualCT2Melzjt[z][j][t]=FeasvalsDualRangeSumXijt[l];
//	l++;
//	}
//	}
//	}
//
//	for (i=0;i<imax;i++){
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	S2valsDualSC2_Cizt[i][z][t]=FeasvalsDualRangeSumXijt[l];
//	l++;
//	}
//	}
//	}
//
//	for (k=0;k<kmax;k++){
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	S2valsDualSD2_Dkzt[k][z][t]=FeasvalsDualRangeSumXijt[l];
//	l++;
//	}
//	}
//	}
//
//	for (i=0;i<imax;i++){
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	S2valsDualSC_Cizt[i][z][t]=FeasvalsDualRangeSumXijt[l];
//	l++;
//	}
//	}
//	}
//
//	for (k=0;k<kmax;k++){
//	for (z=0;z<zmax;z++){
//	for (t=0;t<tmax;t++){
//	S2valsDualSD_Dkzt[k][z][t]=FeasvalsDualRangeSumXijt[l];
//	l++;
//	}
//	}
//	}
//	*/
//
//	return 0;
//}
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
int CreateBendersOptimalityCut(IloExpr expr101, IloNumVarArray X_vj, IloNumVarArray X_mj, IloNumVarArray Zn) {
	//double SumB_j = 0;
	//double SumLamda = 0;
	for (j = 0; j < jmax; j++) {
		//SumB_j = 0;
		for (i = 0; i < imax; i++) {
			//SumB_j = SumB_j + Beta_ijValue[i][j];
			expr101 += Beta_ijValue[i][j] * X_vj[j];
			expr101 += Gamma_ijValue[i][j] * X_mj[j];
		}
		//OptCutCoefs.push_back(SumB_j);
		expr101 += Lamda1_iValue[j] + Lamda2_iValue[j];
		//SumLamda = SumLamda + Lamda1_iValue[j];
	}
	//OptCutCoefs.push_back(SumLamda);
	for (n = 0; n < 1; n++) {
		expr101 -= Zn[n];
	}



	return 0;
}
int AddBendersOptimalityCutToMaster(IloEnv env, IloExpr expr101, IloModel modelMaster_ptr, IloRangeArray BendersCuts) {
	//--------------ADD BENDERS  CUT TO MASTER----------------
	//If FeasOrOpt=0, then a FEASIBILITY CUT is added
	//If FeasOrOpt=1, then a OPTIMALITY CUT is added
	char MasterCut[60];
	sprintf(MasterCut, "OptimalityCut(iter%d)", loop);
	BDOptCuts++;
	double LB101 = 0, UB101 = IloInfinity;
	IloRange CTMaster(env, LB101, expr101, UB101, MasterCut);
	BendersCuts.add(CTMaster);
	modelMaster_ptr.add(CTMaster);
	CutsPerIteration++;

	return 0;
}
int CreateBendersFeasibilityCut(int i_ptr, IloExpr expr101, IloNumVarArray X_vj, IloNumVarArray X_mj) {

	for (j = 0; j < jmax; j++) {
		expr101 += Beta_ijValue[i_ptr][j] * X_vj[j];
		expr101 += Gamma_ijValue[i_ptr][j] * X_mj[j];
	}
	expr101 += Lamda1_iValue[i_ptr] + Lamda2_iValue[i_ptr];

	return 0;
}
int AddBendersFeasibilityCutToMaster(IloEnv env, int i_ptr, IloExpr expr101, IloModel modelMaster_ptr, IloRangeArray BendersCuts, int l_ptr) {
	//--------------ADD BENDERS  CUT TO MASTER----------------
	//If FeasOrOpt=0, then a FEASIBILITY CUT is added
	//If FeasOrOpt=1, then a OPTIMALITY CUT is added
	char MasterCut[60];

	sprintf(MasterCut, "FeasibilityCut(iter%d,i%d,l%d)", loop, i_ptr, l_ptr);
	BDFeasCuts++;

	double LB101 = 0, UB101 = IloInfinity;
	IloRange CTMaster(env, LB101, expr101, UB101, MasterCut);
	BendersCuts.add(CTMaster);
	modelMaster_ptr.add(CTMaster);
	CutsPerIteration++;

	return 0;
}
int PrintBeta() {
	std::ostringstream Coef_Beta_ij;
	Coef_Beta_ij << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\Proposed_Alg\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\Proposed_Alg - Beta_ij.txt";
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
	Coef_Lamda1_i << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\Proposed_Alg\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\Proposed_Alg - Lamda1_i.txt";
	std::string FileNameCoef_Lamda1_i = Coef_Lamda1_i.str();
	std::ofstream fsCoef_Lamda1_i;
	fsCoef_Lamda1_i.open(FileNameCoef_Lamda1_i.c_str(), std::ios::out);
	for (j = 0; j < jmax; j++) {
		fsCoef_Lamda1_i << Lamda1_iValue[j] << "\t";
	}
	fsCoef_Lamda1_i.close();


	return 0;
}
int BendersIteration(IloEnv env, IloModel modelMaster_ptr, IloModel modelDualSlave_ptr, IloNumVarArray X_vj, IloNumVarArray X_mj, IloNumVarArray Zn, IloNum SlackValuesMasterCons, IloNumArray SlackValues, IloRangeArray Con_Master_1n, IloRangeArray Con_Master_2n, IloRangeArray Con_Master_3i, IloRangeArray BendersCuts) {

	bool InfeasibleMaster = false;
	int status, startMaster, stopMaster, startSlave, stopSlave;
	int CoveredVariables;
	//IloCplex cplexDualSlave_ptr(env);
	IloCplex cplexMaster_ptr(env);

	//cplexDualSlave_ptr.extract(modelDualSlave_ptr);
	//cplexDualSlave_ptr.exportModel("modelDualSlave.lp");

	cplexMaster_ptr.extract(modelMaster_ptr);
	cplexMaster_ptr.exportModel("modelMaster1.lp");

	double DTransposeY = 0, DualSlaveObjFunction = 0, PrimalSlaveObjFunction = 0;
	double BestSlaveObj = 100;
	bool FeasCutForNodeAdded_i[imax];
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
	OptCutCoefs.clear();

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
		/*
		status=UpdateSlaveRHS();
		if (status != 0){
		Found_Error("UpdateSlaveRHS");
		return -1;
		}
		*/

		/*status = UpdateDualSlaveObjective();
		if (status != 0) {
		Found_Error("UpdateDualSlaveObjective");
		return -1;
		}*/
		startSlave = clock();
		for (i = 0; i < imax; i++) {
			status = Solve_Dual_Slave(i);
			if (status != 0) {
				Found_Error("Solve_Dual_Slave");
				return -1;
			}
		}
		stopSlave = clock();
		DurationSlave += (long double)(stopSlave - startSlave) / CLOCKS_PER_SEC;
		j = 0;

		for (i = 0; i < imax; i++) {
			if (status_dual[i] == 1) {//--IF DSPi IS FEASIBLE FOR ALL i
				j++;
			}
			FeasCutForNodeAdded_i[i] = false;
		}
		if (j == jmax) {//---------IF DUAL SLAVE IS FEASIBLE-----
			status = Dual_Slave_Bounded(env, &DTransposeY, &DualSlaveObjFunction, &PrimalSlaveObjFunction);
			if (status != 0) {
				Found_Error("Dual_Slave_Bounded");
				return -1;
			}

			/*status = PrintBeta();
			if (status != 0) {
				Found_Error("PrintBeta");
				return -1;
			}*/


			////status=GetExtremePointOfDSP(cplexDualSlave_ptr);
			//if (status != 0) {
			//	Found_Error("GetExtremePointOfDSP");
			//	return -1;
			//}

			IloExpr expr101(env);
			status = CreateBendersOptimalityCut(expr101, X_vj, X_mj, Zn);
			if (status != 0) {
				Found_Error("CreateBendersOptimalityCut");
				return -1;
			}

			status = AddBendersOptimalityCutToMaster(env, expr101, modelMaster_ptr, BendersCuts);//if =1, then adds optimality cut
			if (status != 0) {
				Found_Error("AddBendersOptimalityCutToMaster");
				return -1;
			}
			expr101.end();
		}
		else { //------------- IF DUAL SLAVE PROBLEM IS UNBOUNDED------------
			status = Dual_Slave_Unbounded(env);
			if (status != 0) {
				Found_Error("Dual_Slave_Unbounded");
				return -1;
			}
			l = 0;
			bool Even = false, Odd = false;
			for (i = 0; i < imax; i++) {
				if (status_dual[i] == 0 && l < MaxFeasibilityCutsAdded && FeasCutForNodeAdded_i[i] == false) {//find the nonempty set I', such that DSPi is unbounded && l<jmax - 7,  && l<MaxFeasibilityCutsAdded
					/*if (i % 2 == 0) {
						Even = true;
					}
					else
					{
						Odd = true;
					}
					if (i % 2 == 0 || Even == false) {*/
					bool CloseNodeAdded = false;
					for (j = 0; j < jmax; j++) {
						if ((Distance_ij[i][j] < m_standard || Distance_ij[j][i] < m_standard) && FeasCutForNodeAdded_i[j] == true) {
							CloseNodeAdded = true;
						}
					}
					if (CloseNodeAdded == false) {
						IloExpr expr101(env);
						status = CreateBendersFeasibilityCut(i, expr101, X_vj, X_mj);//if =0, then creates feasibility cut
						if (status != 0) {
							Found_Error("CreateBendersFeasibilityCut");
							return -1;
						}

						status = AddBendersFeasibilityCutToMaster(env, i, expr101, modelMaster_ptr, BendersCuts, l);//if =0, then adds feasibility cut
						if (status != 0) {
							Found_Error("AddBendersFeasibilityCutToMaster");
							return -1;
						}
						expr101.end();
						FeasCutForNodeAdded_i[i] = true;
						l++;
					}
					//}
				}
			}

		}//end of else



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
		//cout << "OptimalObjFunctionFirstTerm=" << OptimalObjFunctionFirstTerm << endl;
		//cout << "OptimalObjFunctionSecondTerm=" << OptimalObjFunctionSecondTerm << endl;
		//cout << "PercentOfSecondTerm=" << abs(OptimalObjFunctionSecondTerm) / (OptimalObjFunctionFirstTerm + OptimalObjFunctionSecondTerm) << endl;
		/*cout << "UpperBound=" << UpperBound << endl;
		cout << "LowerBound=" << LowerBound << endl;
		cout << "LowerBoundGlobal=" << LowerBoundGlobal << endl;
		cout << "Gap=" << Gap * 100 << "%" << endl;*/

		//cout << "-----------------" << endl;
		//cout << "------END OF ITERATION--------" << endl;

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
	os << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\Proposed_Alg\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\Proposed_Alg - OptimalSolution.txt";
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
	fsOptimalSolution << "OptimalObjFunctionFirstTerm= " << OptimalObjFunctionFirstTerm << std::endl;
	fsOptimalSolution << "OptimalObjFunctionSecondTerm= " << OptimalObjFunctionSecondTerm << std::endl;
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
	LowerBound << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\Proposed_Alg\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\Proposed_Alg - LowerBound.txt";
	std::string FileNameLB = LowerBound.str();
	std::ofstream fsLowerBound;
	fsLowerBound.open(FileNameLB.c_str(), std::ios::out);
	for (i = 0; i < LowerBoundArray.size(); i++) {
		fsLowerBound << LowerBoundArray.at(i) << std::endl;
	}
	fsLowerBound.close();

	std::ostringstream UpperBound;
	UpperBound << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\Proposed_Alg\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\Proposed_Alg - UpperBound.txt";
	std::string FileNameUB = UpperBound.str();
	std::ofstream fsUpperBound;
	fsUpperBound.open(FileNameUB.c_str(), std::ios::out);
	for (i = 0; i < UpperBoundArray.size(); i++) {
		fsUpperBound << UpperBoundArray.at(i) << std::endl;
	}
	fsUpperBound.close();

	std::ostringstream LowerBoundGlobal;
	LowerBoundGlobal << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\Proposed_Alg\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\Proposed_Alg - LowerBoundGlobal.txt";
	std::string FileNameUBG = LowerBoundGlobal.str();
	std::ofstream fsLowerBoundGlobal;
	fsLowerBoundGlobal.open(FileNameUBG.c_str(), std::ios::out);
	for (i = 0; i < LowerBoundGlobalArray.size(); i++) {
		fsLowerBoundGlobal << LowerBoundGlobalArray.at(i) << std::endl;
	}
	fsLowerBoundGlobal.close();


	std::ostringstream dTransY;
	dTransY << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\Proposed_Alg\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\Proposed_Alg - DTrasnposeY.txt";
	std::string FileNameDTY = dTransY.str();
	std::ofstream fsdTransY;
	fsdTransY.open(FileNameDTY.c_str(), std::ios::out);
	for (i = 0; i < dTy.size(); i++) {
		fsdTransY << dTy.at(i) << std::endl;
	}
	fsdTransY.close();

	std::ostringstream cTransX;
	cTransX << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\Proposed_Alg\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\Proposed_Alg - CTrasnposeX.txt";
	std::string FileNameCTX = cTransX.str();
	std::ofstream fscTransX;
	fscTransX.open(FileNameCTX.c_str(), std::ios::out);
	for (i = 0; i < cTx.size(); i++) {
		fscTransX << cTx.at(i) << std::endl;
	}
	fscTransX.close();

	std::ostringstream bTransU;
	bTransU << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\Proposed_Alg\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\Proposed_Alg - BTrasnposeU.txt";
	std::string FileNameBTU = bTransU.str();
	std::ofstream fsbTransU;
	fsbTransU.open(FileNameBTU.c_str(), std::ios::out);
	for (i = 0; i < bTu.size(); i++) {
		fsbTransU << bTu.at(i) << std::endl;
	}
	fsbTransU.close();

	std::ostringstream CurrentTheta;
	CurrentTheta << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\Proposed_Alg\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\Proposed_Alg - CurrentTheta.txt";
	std::string FileNameCurrentTheta = CurrentTheta.str();
	std::ofstream fsCurrentTheta;
	fsCurrentTheta.open(FileNameCurrentTheta.c_str(), std::ios::out);
	for (i = 0; i < zCurrent.size(); i++) {
		fsCurrentTheta << zCurrent.at(i) << std::endl;
	}
	fsCurrentTheta.close();

	std::ostringstream BestPrimalSlaveObj;
	BestPrimalSlaveObj << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\Proposed_Alg\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\Proposed_Alg - BestPrimalSlaveObjSoFar.txt";
	std::string FileNameBPSO = BestPrimalSlaveObj.str();
	std::ofstream fsBestPrimalSlaveObj;
	fsBestPrimalSlaveObj.open(FileNameBPSO.c_str(), std::ios::out);
	for (i = 0; i < BestPrimalSlaveObjSoFar.size(); i++) {
		fsBestPrimalSlaveObj << BestPrimalSlaveObjSoFar.at(i) << std::endl;
	}
	fsBestPrimalSlaveObj.close();

	std::ostringstream BestDualSlaveObj;
	BestDualSlaveObj << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\Proposed_Alg\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\Proposed_Alg - BestDualSlaveObjSoFar.txt";
	std::string FileNameBDSO = BestDualSlaveObj.str();
	std::ofstream fsBestDualSlaveObj;
	fsBestDualSlaveObj.open(FileNameBDSO.c_str(), std::ios::out);
	for (i = 0; i < BestDualSlaveObjSoFar.size(); i++) {
		fsBestDualSlaveObj << BestDualSlaveObjSoFar.at(i) << std::endl;
	}
	fsBestDualSlaveObj.close();



	std::ostringstream TimePath;
	TimePath << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\Proposed_Alg\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\Proposed_Alg - Time.txt";
	std::string FileNameTime = TimePath.str();
	std::ofstream fsTime;
	fsTime.open(FileNameTime.c_str(), std::ios::out);
	for (i = 0; i < Time.size(); i++) {
		fsTime << Time.at(i) << std::endl;
	}
	fsTime.close();

	std::ostringstream DataDistance;
	DataDistance << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\Proposed_Alg\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\Proposed_Alg - Distance.txt";
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
	Data << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\Proposed_Alg\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\Proposed_Alg - Data.txt";
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
	//SlackVals << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\Proposed_Alg\\Proposed_Alg - SlackValuesBendersCuts.txt";
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
	/*int line = 1, index=0;
	std::ostringstream SlackValsBendersCuts;
	SlackValsBendersCuts << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\Proposed_Alg\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\Proposed_Alg - SlackValuesBendersCuts.txt";
	std::string FileNameSlackMaster = SlackValsBendersCuts.str();
	std::ofstream fsSlackBendersCuts;
	fsSlackBendersCuts.open(FileNameSlackMaster.c_str(), std::ios::out);
	for (i = 0; i < SlackValuesOfBendersCuts.size(); i++) {
		fsSlackBendersCuts << SlackValuesOfBendersCuts.at(i) << "\t";
		index++;
		if (index == line) {
			index = 0;
			line++;
			fsSlackBendersCuts << std::endl;
		}

	}
	fsSlackBendersCuts.close();

	std::ostringstream OptCutCoefficients;
	OptCutCoefficients << "D:\\Antonis\\PhD_Examples\\Results_Ambulance\\NewDataSet\\Proposed_Alg\\" << imax << "nodesDataset\\Case" << Case << "\\Example" << Example << "\\Proposed_Alg - OptCutCoefficients.txt";
	std::string FileNameOptCutCoefficients = OptCutCoefficients.str();
	std::ofstream fsOptCutCoefficients;
	fsOptCutCoefficients.open(FileNameOptCutCoefficients.c_str(), std::ios::out);
	for (i = 0; i < OptCutCoefs.size(); i++) {
		fsOptCutCoefficients << OptCutCoefs.at(i) << "\t";
		if ((i+1)%(imax+1) == 0 && i!=0) {
			fsOptCutCoefficients << std::endl;
		}

	}
	fsOptCutCoefficients.close();*/

	return 0;
}

int main(int argc, char** argv)
{
	int  stop, status;
	for (Case = 1; Case <= 1; Case++) {
		for (Example = 2; Example <= 2; Example++) {
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


				IloNumVarArray AllVars(env, 0);

				//--------Declare Master constraints-------------
				IloRangeArray Con_Master_1n(env, 0);
				IloRangeArray Con_Master_2n(env, 0);
				IloRangeArray Con_Master_3i(env, 0);
				//--------Declare Dual Objective function-------------
				//IloObjective Dual_objective(env, 0);

				//--------Declare Array of Benders Cuts Added in Master Problem-------------
				IloRangeArray BendersCuts(env, 0);

				//--------Declare DUAL variables (Variables of DSP)----------------


				//--------Declare dual variables of each constraint----------------
				IloNumArray FeasvalsDualRangeSumXijt(env, 0);
				IloNumArray SlackValues(env, 0);
				IloNum SlackValuesMasterCons = 0;


				//--------Construct models----------------
				//IloModel modelSlave1 (env);

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
				/*
				status = do_dual_slave();
				if (status != 0) {
				Found_Error("do_dual_slave");
				return -1;
				}
				*/

				status = BendersIteration(env, modelMaster, modelDualSlave, X_vj, X_mj, Zn, SlackValuesMasterCons, SlackValues, Con_Master_1n, Con_Master_2n, Con_Master_3i, BendersCuts);
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
			/*X_vj.end();
			X_mj.end();
			Zn.end();
			modelDualSlave.end();
			modelMaster.end();
			AllVars.end();
			Con_Master_1n.end();
			Con_Master_2n.end();
			BendersCuts.end();
			FeasvalsDualRangeSumXijt.end();
			SlackValues.end();*/
			//SlackValuesMasterCons.end();

			printf("Code terminated successfully \n");
			printf("Execution time = %Lf seconds\n", Duration);

		}
	}


	return 0;

} //End main