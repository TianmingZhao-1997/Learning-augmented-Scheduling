// The version contains a working and refactored OfflineRelaxedMakespan (verified)
// The version contains a working and refactored Online_KnownErrorMakespan (verified)
// The version contains a working Online_UnknownErrorMakespan 
// The version contains a working Online_ClassicMakespan 
// Tests are refactored
/*
    This is the source code for TC algorithms (dynamic scheduling) 
        4 algorithms:
    (1) The improved 2-relaxed procedure as the performance baseline
    (2) The classic O(\log m)-competitive procedure (requires the knowledge of the lower bound on job size, e.g., 1.0)
    (3) The online scheduling with known error
    (4) The online scheduling with unknon error
*/
#include <iostream>
#include <fstream>
#include <random>
#include <vector>
#include <set>
#include <queue>
#include <algorithm>
#include <iomanip>

using namespace std;

/* Constants */
const int N = 512;                      // number of jobs
const double MAX_JOB_SIZE = 1024;       // maximum job size
const double MAX_SPEED = 64;            // maximum machine speed
const double MAX_RELEASE_TIME = 64;     // maximum job release time

/* Global Variable */
const int RAND_SEED = 0;          // randomization in problem generation
default_random_engine eng (RAND_SEED);  // randomization in problem generation

/* Declare a problem instance */
struct Problem {
    int n;                              // n: number of jobs
    int m;                              // m: number of machines

    vector<double> jobSize;             // of size n
    vector<double> releaseTime;         // of size n
    vector<double> speed;               // of size m

    /* Estimated size */
    double eta;                         // the total prediction error
    vector<double> jobSizePrediction;   // of size n
};

struct Status {
    Problem *I;

    int m, n; // m: number of machines, n: number of jobs
    int sup;  // critical threshold indicating fast machines. The variable is computed upon Status initialization

    /* Execution parameters */
    set<pair<double, int>> waitingJobs;         // set of jobs not begin
    set<pair<double, int>> slowMachineJobs;     // set of jobs begin at slow machines (i > sup) 
    set<pair<double, int>> largeProcessingJobs; // set of jobs begin at a machine not fast enough
    
    double eta;                                 // the prediction error (for scheduling with known error)
    double eta_e;                               // the prediction error estimate (for scheduling with unknwon error)
    vector<double> eJobSize;                    // job size estimate (of size n)
    vector<int> assigned;                       // which machine job j is assigned to (of size n)
    vector<int> processing;                     // which job machine i is processing (of size m)
    vector<double> complete_time;               // completion time for machine i (of size m)
    vector<bool> completed_job;                 // whether job j is completed (of size m)

    double d = 0;                               // makespan estimate
    int num_completed_jobs = 0;                 // the number of completed jobs

    set<pair<double, int>> Q;                   // event queue: an event is a pair (time, machine_id)
    double base_time = 0;                       // the absolute time that is used as a relative starting time point

    double TOTAL_MAKESPAN = 0;                  // the final returned value

    Status (Problem *input) {
        I = input;
        m = I->m, n = I->n;
        eta = I->eta;
        sup = compute_sup ();
    }

    void init_Status () {
        eJobSize = vector<double>(n, -1);
        assigned = vector<int>(n, -1);
        processing = vector<int>(m, -1);
        complete_time = vector<double>(m, -1);
        completed_job = vector<bool>(n, false);
    }

    void freeMachine (int machineIndex) {
        // Free a machine from a machine's perspective
        Q.erase (make_pair(complete_time[machineIndex], machineIndex));
        complete_time[machineIndex] = -1;
        processing[machineIndex] = -1;
    }

    void freeJob (int jobIndex) {
        // Free a job from a job's perspective
        assigned[jobIndex] = -1;
    }

    void completeJob (int jobCompleted) {
        num_completed_jobs ++;
        // erase the job from the system
        completed_job [jobCompleted] = true;
        eraseJob (jobCompleted);
    }

    void beginJob (int jobIndex, int machineIndex) {
        // Move the job to the appropraite set
        eraseJob (jobIndex);
        // Insert the job into the right set
        if (I->speed[machineIndex] * d < eJobSize[jobIndex]){
            largeProcessingJobs.insert(make_pair(eJobSize[jobIndex], jobIndex));
        } else if (machineIndex > sup){
            slowMachineJobs.insert(make_pair(eJobSize[jobIndex], jobIndex));
        }
        assigned[jobIndex] = machineIndex;
    }

    void startRunning (int jobIndex, int machineIndex, double t) {
        // Start running jobIndex on machineIndex at time t
        // This function is called if a job is migrated or initially started running on the machine
        double c_time = t + (I->jobSize)[jobIndex] / (I->speed)[machineIndex];
        Q.insert(make_pair(c_time, machineIndex));
        complete_time[machineIndex] = c_time;
        processing[machineIndex] = jobIndex;
    }

    void shift_Status (double t) {
        // the complete_time and the corresponding event must be shift to the left for time t
        set<pair<double, int>> new_Q;
        for (const pair<double, int>& j_pair: Q) {
            complete_time[j_pair.second] -= t;
            new_Q.insert (make_pair(complete_time[j_pair.second], j_pair.second));
        }
        Q = new_Q;
        base_time += t;
    }

    void idleMachine (int machineIndex) {
        int jobIndex = processing[machineIndex];
        if (jobIndex < 0) return ;
        // Move the job to waitingJobs
        eraseJob (jobIndex);
        waitingJobs.insert (make_pair(eJobSize[jobIndex], jobIndex));
        // Idle the machine
        freeMachine (machineIndex);
        freeJob (jobIndex);
    }

    void eraseJob (int jobIndex) {
        // Clear the job from waitingJobs, slowMachineJobs, and largeProcessingJobs
        pair<double, int> job = make_pair(eJobSize[jobIndex], jobIndex);
        waitingJobs.erase(job);
        slowMachineJobs.erase(job);
        largeProcessingJobs.erase(job);
    }

    void preemptJobs () {
        // Make sure all jobs are preempted
        // All jobs from event Q go to waitingJobs
        for (const pair<double, int>& event: Q) {
            int machineIndex = event.second;
            int jobIndex = processing[machineIndex];
            if (jobIndex >= 0) {
                waitingJobs.insert (make_pair(eJobSize[jobIndex], jobIndex));
            }
        }
        // Erase all jobs from slowMachineJobs and largeProcessingJobs
        slowMachineJobs.clear();
        largeProcessingJobs.clear();
    }

    void process (int jobIndex, int machineIndex, double t) { // called inside a stage processing when a machine becomes idle
        // Process Job with jobIndex on machine with machineIndex on time t
        if (jobIndex < 0) return ;
        // Deal with the case that the job is currently being processed 
        if(assigned[jobIndex] >= 0) {
            idleMachine (assigned[jobIndex]);
        }
        // Insert the job into the right set
        beginJob (jobIndex, machineIndex);
        // Update the status
        startRunning (jobIndex, machineIndex, t);
    }

    void init_process (int jobIndex, int machineIndex, double t) { // called at the beginning of a stage
        if (jobIndex < 0) {
            // Release the job running on machine with machineIndex IF it is assigned to this machine
            int cur_job = processing[machineIndex];
            if (cur_job >= 0 && assigned[cur_job] == machineIndex) {
                freeJob (cur_job);
            }
            freeMachine (machineIndex);
            return ;
        }
        // Process Job with jobIndex on machine with machineIndex on time t
        if (processing [machineIndex] == jobIndex) {
            // Insert the job into the right set
            beginJob (jobIndex, machineIndex); // Resume on the same machine, do not call startRunning
            return ;
        }
        // Deal with the case that the job is currently being processed on the current machine
        // Deal with the currently running job
        if (processing[machineIndex] >= 0) {
            freeJob (processing[machineIndex]);
            freeMachine (machineIndex);
        }
        // Deal with the job
        if (assigned[jobIndex] >= 0) {
            // Idle the machine
            int machineToIdle = assigned[jobIndex];
            freeJob (jobIndex);
            freeMachine (machineToIdle);
        }
        // Insert the job into the right set
        beginJob (jobIndex, machineIndex);
        // Update the status
        startRunning (jobIndex, machineIndex, 0);
    }

    void updateJobSizeEstimates () {
        set<pair<double, int>> newWaitingJobs;
        for (const pair<double, int>& job: waitingJobs) {
            newWaitingJobs.insert (make_pair(eJobSize[job.second], job.second));
        }
        waitingJobs = newWaitingJobs;
    }

    /* Helper Function */
    double compute_sup () {
        double totalSpeed = 0;
        for(const double& s: I->speed) totalSpeed += s;
        int sup = -1; double curTotalSpeed = 0;
        while(curTotalSpeed < 0.5 * totalSpeed){
            sup++;
            curTotalSpeed += I->speed[sup];
        }
        return sup;
    }

    double max_jobSizeEstimate () {
        // Return the maximum jobSize estimate from waitingJobs set
        double res = 0;
        for (const pair<double, int>& job: waitingJobs) res = max(res, job.first);
        return res;
    }

    bool hasActiveJobs () {
        return (!waitingJobs.empty() || !slowMachineJobs.empty() || !largeProcessingJobs.empty());
    }

    bool impossibleToComplete () {
        bool impossible = hasActiveJobs ();
        if(!impossible){
            // Check all fast machines
            for(int i = 0; i <= sup; i++){
                if(processing[i] >= 0){
                    double startTime = complete_time[i] - I->jobSize[processing[i]]/I->speed[i];
                    if(startTime >= d || (i == 0 && startTime < d)){
                        impossible = true;
                        break;
                    }
                }
            }
        }
        return impossible;
    }

    bool ifValidComputed () {
        for (int j = 0; j < n; j++) {
            if (!completed_job[j]) return false;
        }
        return true;
    }

    bool validStatus () {
        for (const pair<double, int>& e: Q) {
            if (e.first < 0) {
                cout << "INCORRECT INTERMEDIATE RESULT" << endl;
                cout << "e.first = " << e.first << endl;
                exit(1);
            }
        }
        return true;
    }
};

/* Procedure Declaration */

/* Simulation Code */
void simulation (int num_instance, int num_repeat);
void simulation_eta (int num_instance, int num_repeat, double (*algo)(Problem& prob));

/* Online Scheduling with a Known / Unknown Error */
int getJob (int i, const Status& S);

/* Online Scheduling with a Unknown Error */
bool Online_UnknownErrorProcedure (Status& S, double deadline);
double Online_UnknownErrorMakespan (Problem& instance);

/* Online Scheduling with a Known Error */
bool Online_KnownErrorProcedure (Status& S, double deadline);
double Online_KnownErrorMakespan (Problem& instance);

/* Online Classic Scheduling */
int getJobClassic (int i, const Status& S);
bool Online_ClassicProcedure (Status& S, double deadline);
double Online_ClassicMakespan (Problem& instance);

/* The Offline Approximation Algorithm based on Binary Search */
int getJob_improved2_Relaxed (int i, const Status& S);
double Offline_BisectionSearch (const Status& S);
bool Improved2_RelaxedProcedure (Status& S, double deadline);
double OfflineRelaxedMakespan (Problem& instance);

/* Common Subroutines */
void processEvent (Status& S);
set<pair<double, int>>::iterator findJob (int i, const Status& S, const set<pair<double, int>>& jobSet);
int getJobIndex (const set<pair<double, int>>::iterator& it1, const set<pair<double, int>>::iterator& it2, const Status& S);
void reInitializeEventQOffline (Status& S);
void reInitializeEventQOnline (Status& S);
void reInitializeEventQOnlineClassic (Status& S);
double processJobRelease (Status& S, int j);
void pauseRunning (Status& S, double time);

/* Problem associated procedures */
void randProblem (Problem& instance, int m, int n);
void extendProblem (Problem& instance, int new_m);
void predictSize (Problem& instance, double eta);
void printProblem (const Problem& instance);
Problem loadProblem (const string& fileName);

/* Printing procedures */
void print_set (const set<pair<double, int>>& to_visualize);
void print_vector (const vector<double>& to_visualize);
void print_vector (const vector<int>& to_visualize);
void print_vector (const vector<bool>& to_visualize);
void print (const Status& S);
void print_data (double etas[], double ratios[][8][3]);

/* Tests */
double makespan_lowerbound (const Problem& prob);
void test ();
void test_Algorithm (double (*algo)(Problem& prob));
void test_OfflineRelaxedMakespan ();
void test_OnlineKnownErrorMakespan ();
void test_OnlineUnknownErrorMakespan ();
void test_OnlineClassicMakespan ();
void test_all ();
void debug_problem ();

int main()
{
    //test ();
    //test_OfflineRelaxedMakespan ();
    //test_OnlineKnownErrorMakespan ();
    //test_OnlineUnknownErrorMakespan ();
    //test_OnlineClassicMakespan ();
    //test_all ();
    //simulation (1000, 10);
    //debug_problem ();
    simulation_eta (100, 10, Online_UnknownErrorMakespan);

    return 0;
}

/* Procedure Implementations */
/* Simulation with default n and m with varying eta */
void simulation_eta (int num_instance, int num_repeat, double (*algo)(Problem& prob))
{
    const int num_etas = 10;
    const int default_log_m = 5;
    const int default_m = (1 << default_log_m);
    double etas[num_etas] = {1, 2, 4, 8, 16, 32, 64, 128, 256, MAX_JOB_SIZE * 100.0};
    const int default_n = 256;

    double dratios[num_etas][num_instance];
    for (int k_eta = 0; k_eta < num_etas; k_eta++) {
        for (int instance_id = 0; instance_id < num_instance; instance_id ++) {
            dratios[k_eta][instance_id] = 0;
        }
    }

    for(int instance_id = 0; instance_id < num_instance; instance_id++) {
        Problem instance;
        randProblem(instance, default_m, default_n);

        // Make the problem static
        /*
        for (int j = 0; j < instance.n; j++) instance.releaseTime [j] = 0;
        */

        double opt_makespan_d = OfflineRelaxedMakespan(instance);

        for(int k_eta = 0; k_eta < num_etas; k_eta++) {
            double eta = etas[k_eta];
            double makespan_dynamic = 0;

            // Repeat num_repeat times
            for(int repeat_id = 0; repeat_id < num_repeat; repeat_id++) {
                predictSize (instance, eta);
                double makespan = algo (instance);
                makespan_dynamic += makespan;
            }
            makespan_dynamic /= num_repeat;

            dratios[k_eta][instance_id] = makespan_dynamic / opt_makespan_d;
        }
    }

    // Output the experimental data
    for(int k_eta = 0; k_eta < num_etas; k_eta++) {
        for (int instance_id = 0; instance_id < num_instance; instance_id++) {
            if (instance_id > 0) cout << ",";
            cout << dratios [k_eta][instance_id];
        }
        cout << endl;
    }
}

/* Simulation Code */
void simulation (int num_instance, int num_repeat)
{
    const int num_etas = 10;
    const int max_log_m = 7;
    double etas[num_etas] = {1, 2, 4, 8, 16, 32, 64, 128, 256, MAX_JOB_SIZE * 100.0};

    // ratios[eta][log_m][i]:
    //   i = 0: online_know_error
    //   i = 1: online_unknow_error
    //   i = 2: online_classic
    double dratios[num_etas][max_log_m+1][3], sratios[num_etas][max_log_m+1][3]; // average competitive ratio
    double dratios_max[num_etas][max_log_m+1][3], sratios_max[num_etas][max_log_m+1][3]; // max competitive ratio
    for(int k_eta = 0; k_eta < num_etas; k_eta++){
        for(int log_m = 1; log_m <= max_log_m; log_m++){
            for(int k = 0; k < 3; k++){
                dratios[k_eta][log_m][k] = 0;
                sratios[k_eta][log_m][k] = 0;
                dratios_max[k_eta][log_m][k] = 0;
                sratios_max[k_eta][log_m][k] = 0;
            }
        }
    }

    int total_problem_instances = 0;
    // Fix the job size
    int n = 256; // number of jobs = 256

    for(int instance_id = 0; instance_id < num_instance; instance_id++) {
        total_problem_instances ++;
        //cout << "Running problem " << (instance_id + 1) << endl;
        // Generate an instance
        Problem instance;
        randProblem(instance, 2, n);

        for(int log_m = 1; log_m <= max_log_m; log_m += 1) { // log of number of machines
            int m = (1 << log_m);
            extendProblem(instance, m);
            // Dynamic Scheduling
            double opt_makespan_d = OfflineRelaxedMakespan(instance);
            double online_classic_d = Online_ClassicMakespan(instance);
            // Static Scheduling
            Problem static_prob = instance;
            for (int i = 0; i < static_prob.n; i++) static_prob.releaseTime[i] = 0;
            double opt_makespan_s = OfflineRelaxedMakespan(static_prob);
            double online_classic_s = Online_ClassicMakespan(static_prob);

            for(int k_eta = 0; k_eta < num_etas; k_eta++) {
                double eta = etas[k_eta];
                double online_know_error_dynamic = 0, online_unknow_error_dynamic = 0;
                double online_know_error_static = 0, online_unknow_error_static = 0;

                // Repeat num_repeat times
                for(int repeat_id = 0; repeat_id < num_repeat; repeat_id++) {
                    predictSize(instance, eta);
                    // Solve instance two times
                    double d_online_know_error = Online_KnownErrorMakespan(instance);
                    double d_online_unknow_error = Online_UnknownErrorMakespan(instance);

                    online_know_error_dynamic += d_online_know_error;
                    online_unknow_error_dynamic += d_online_unknow_error;

                    dratios_max[k_eta][log_m][0] = max (dratios_max[k_eta][log_m][0], d_online_know_error / opt_makespan_d);
                    dratios_max[k_eta][log_m][1] = max (dratios_max[k_eta][log_m][1], d_online_unknow_error / opt_makespan_d);

                    // Static Scheduling (use the job size predictions)
                    static_prob.eta = eta;
                    static_prob.jobSizePrediction = instance.jobSizePrediction;

                    double s_online_know_error = Online_KnownErrorMakespan(static_prob);
                    double s_online_unknow_error = Online_UnknownErrorMakespan(static_prob);

                    online_know_error_static += s_online_know_error;
                    online_unknow_error_static += s_online_unknow_error;

                    sratios_max[k_eta][log_m][0] = max (sratios_max[k_eta][log_m][0], s_online_know_error / opt_makespan_s);
                    sratios_max[k_eta][log_m][1] = max (sratios_max[k_eta][log_m][1], s_online_unknow_error / opt_makespan_s);
                }
                online_know_error_dynamic /= num_repeat; online_unknow_error_dynamic /= num_repeat;
                online_know_error_static /= num_repeat; online_unknow_error_static /= num_repeat;

                // no. jobs = num_jobs, no. machines = m, error = eta
                /* Dynamic Scheduling */
                /* Compute competitive ratio(s) */
                double online_classic_ratio = online_classic_d / opt_makespan_d;
                double online_know_ratio = online_know_error_dynamic / opt_makespan_d;
                double online_unknow_ratio = online_unknow_error_dynamic / opt_makespan_d;

                dratios[k_eta][log_m][0] += online_know_ratio;
                dratios[k_eta][log_m][1] += online_unknow_ratio;
                dratios[k_eta][log_m][2] += online_classic_ratio;
                
                dratios_max[k_eta][log_m][2] = max (dratios_max[k_eta][log_m][2], online_classic_ratio);

                /* Static Scheduling */
                online_classic_ratio = online_classic_s / opt_makespan_s;
                online_know_ratio = online_know_error_static / opt_makespan_s;
                online_unknow_ratio = online_unknow_error_static / opt_makespan_s;

                sratios[k_eta][log_m][0] += online_know_ratio;
                sratios[k_eta][log_m][1] += online_unknow_ratio;
                sratios[k_eta][log_m][2] += online_classic_ratio;

                sratios_max[k_eta][log_m][2] = max (sratios_max[k_eta][log_m][2], online_classic_ratio);
            }
        }
    }

    for(int k_eta = 0; k_eta < num_etas; k_eta++) {
        for(int log_m = 1; log_m <= max_log_m; log_m += 1) {
            for(int k = 0; k < 3; k++) {
                dratios[k_eta][log_m][k] /= total_problem_instances;
                sratios[k_eta][log_m][k] /= total_problem_instances;
            }
        }
    }

    // Output the experimental data
    cout << "Static Scheduling: " << endl;
    cout << "Mean competitive ratio: " << endl;
    print_data (etas, sratios);
    cout << "Max competitive ratio: " << endl;
    print_data (etas, sratios_max);
    cout << endl;
    cout << "Dynamic Scheduling: " << endl;
    cout << "Mean competitive ratio: " << endl;
    print_data (etas, dratios);
    cout << "Max competitive ratio: " << endl;
    print_data (etas, dratios_max);
    cout << endl;
}

void print_data (double etas[], double ratios[][8][3])
{
    int num_etas = 10;
    int max_log_m = 7;

    for(int k_eta = 0; k_eta < num_etas; k_eta++){
        cout << "eta = " << ((k_eta < num_etas-1)? to_string(etas[k_eta]):"inf") << ":" << endl;
        /* Print x-axis: log_m */
        cout << "log_m = [";
        for(int log_m = 1; log_m <= max_log_m; log_m += 1){
            if(log_m > 1) cout << ",";
            cout << log_m;
        }
        cout << "]" << endl;
        /* Print Online Knowing Error Competitive Ratio */
        cout << "onlineKnowError = [";
        for(int log_m = 1; log_m <= max_log_m; log_m += 1){
            if(log_m > 1) cout << ",";
            cout << ratios[k_eta][log_m][0];
        }
        cout << "]" << endl;
        /* Print Online Unknowing Error Competitive Ratio */
        cout << "onlineUnknowError = [";
        for(int log_m = 1; log_m <= max_log_m; log_m += 1){
            if(log_m > 1) cout << ",";
            cout << ratios[k_eta][log_m][1];
        }
        cout << "]" << endl;
        /* Print Online Classic Competitive Ratio */
        cout << "onlineClassic = [";
        for(int log_m = 1; log_m <= max_log_m; log_m += 1){
            if(log_m > 1) cout << ",";
            cout << ratios[k_eta][log_m][2];
        }
        cout << "]" << endl;
        cout << endl;
    }
}

/* Online Scheduling with a Unknown Error */
double Online_UnknownErrorMakespan (Problem& instance)
{
    Status S (&instance);
    S.init_Status ();
    S.eta_e = 1.0;

    // Init eJobSize by setting p^e_j = p_j / eta_e
    for (int j = 0; j < S.n; j++) S.eJobSize[j] = max(1.0, S.I->jobSizePrediction[j] / S.eta_e);

    for (int j = 0; j < instance.n; j++) {
        // A new job is released
        double deadline = processJobRelease (S, j);
        // Find the makespan for the current stage
        S.d = S.max_jobSizeEstimate () / S.I->speed[0];
        Online_UnknownErrorProcedure (S, deadline);
    }

    if (!S.ifValidComputed()) {
        cout << "BAD SCHEDULE!" << endl;
        exit(1);
    }

    return S.TOTAL_MAKESPAN;
}

// Online Scheduling with Unknown Error Procedure for processing one stage
bool Online_UnknownErrorProcedure (Status& S, double deadline)
{
    // Initialize the event Q to keep cope with the current status
    reInitializeEventQOnline (S);

    // Process events
    double time = 0;
    while (!S.Q.empty()) {
        double curTime = (*(S.Q.begin())).first; 
        time = max (time, curTime);
        if (time > deadline) {
            return false; // the procedure fails to complete with all job finishes by deadline
        }
        if (time > 2 * S.d) {
            /* Termination of this run */
            time = 2 * S.d;             // The current time is 2 * S.d
            bool impossible = S.impossibleToComplete();

            pauseRunning (S, time);     // Pause and shift timing variables and prepare the next stage processing
            // Initialize eJobSize or S.d and Q for the next stage
            if (impossible) {
                S.d = 2 * S.d;
            } else {
                for (const pair<double, int>& job: S.waitingJobs) {
                    int jobToUpdate = job.second;
                    int machineIndex = S.assigned[jobToUpdate];
                    S.eJobSize[jobToUpdate] = max(2.0 * S.eJobSize[jobToUpdate], 2.0 * (S.I->jobSize[jobToUpdate] - S.I->speed[machineIndex] * S.complete_time[jobToUpdate]));
                }
                S.updateJobSizeEstimates ();
            }
            // Initialize the event Q to keep cope with the current status
            reInitializeEventQOnline (S);
            // Set time to 0 for the next inner_procedure circle
            deadline -= time;           // Shift 2 * S.d amount in time
            time = 0;
            continue;
        }

        // Process the event
        int machine = (*(S.Q.begin())).second; // Record the machine index 
        int jobCompleted = S.processing[machine]; // For checking if we update eta_e
        processEvent (S);

        // Check if we need to update eta_e
        if (S.eta_e < MAX_JOB_SIZE && S.eJobSize[jobCompleted] > S.I->jobSize[jobCompleted]) {
            /* Termination of this run */
            pauseRunning (S, time);     // Pause and shift timing variables and prepare the next stage processing
            S.eta_e = S.eta_e * 2;
            if (S.eta_e * S.eta_e > S.m) {
                // Assume that the prediction error is infinitely large
                for (int j = 0; j < S.n; j++) S.eJobSize[j] = 1.0; 
                S.eta_e = INFINITY;
            } else {
                for (int j = 0; j < S.n; j++) S.eJobSize[j] = max(1.0, S.I->jobSizePrediction[j] / S.eta_e);
            }
            S.updateJobSizeEstimates ();
            // Initialize S.d and Q for the next stage
            S.d = S.max_jobSizeEstimate () / S.I->speed[0];
            // Initialize the event Q to keep cope with the current status
            reInitializeEventQOnline (S);
            // Set time to 0 for the next inner_procedure circle
            deadline -= time;           // Shift 2 * S.d amount in time
            time = 0;
            continue;
        }

        // Machine becomes idle at time
        int jobIndex = getJob (machine, S);
        S.process (jobIndex, machine, time); // If jobIdex == -1, the machine becomes idle
    }

    S.TOTAL_MAKESPAN += min (time, deadline);
    return true;
}

/* Online Scheduling with a Known Error */
double Online_KnownErrorMakespan (Problem& instance)
{
    Status S (&instance);
    S.init_Status ();
    S.eta_e = S.eta;

    // Init eJobSize by setting p^e_j = p_j / eta_e
    for (int j = 0; j < S.n; j++) S.eJobSize[j] = max(1.0, S.I->jobSizePrediction[j] / S.eta_e);

    for (int j = 0; j < instance.n; j++) {
        // A new job is released
        double deadline = processJobRelease (S, j);
        //cout << "Processing job " << j << endl;
        // Find the makespan for the current stage
        S.d = S.max_jobSizeEstimate () / S.I->speed[0];
        //print (S);
        Online_KnownErrorProcedure (S, deadline);
        //print (S);
    }

    if (!S.ifValidComputed()) {
        cout << "BAD SCHEDULE!" << endl;
        exit(1);
    }

    return S.TOTAL_MAKESPAN;
}

// Online Scheduling with Known Error Procedure for processing one stage
bool Online_KnownErrorProcedure (Status& S, double deadline)
{
    // Initialize the event Q to keep cope with the current status
    reInitializeEventQOnline (S);

    // Process events
    double time = 0;
    while (!S.Q.empty()) {
        double curTime = (*(S.Q.begin())).first; 
        time = max (time, curTime);
        if (time > deadline) {
            return false; // the procedure fails to complete with all job finishes by deadline
        }

        //cout << "CurTime = " << curTime << endl;

        if (time > 2 * S.d) {
            //cout << "At termination of this run" << endl;
            /* Termination of this run */
            time = 2 * S.d;             // The current time is 2 * S.d
            bool impossible = S.impossibleToComplete();

            pauseRunning (S, time);     // Pause and shift timing variables and prepare the next stage processing
            // Initialize eJobSize or S.d and Q for the next stage

            //cout << "Running has been paused !" << endl;

            if (impossible) {
                S.d = 2 * S.d;
            } else {
                for (const pair<double, int>& job: S.waitingJobs) {
                    int jobToUpdate = job.second;
                    int machineIndex = S.assigned[jobToUpdate];
                    //cout << "jobToUpdate = " << jobToUpdate << endl;
                    //cout << "machineIndex = " << machineIndex << endl;
                    S.eJobSize[jobToUpdate] = max(2.0 * S.eJobSize[jobToUpdate], 2.0 * (S.I->jobSize[jobToUpdate] - S.I->speed[machineIndex] * S.complete_time[jobToUpdate]));
                }
                //cout << "Jobs in S.waitingJobs have been updated" << endl;
                S.updateJobSizeEstimates ();
            }

            //cout << "S.d or eJobSize has been updated!" << endl;

            // Initialize the event Q to keep cope with the current status
            reInitializeEventQOnline (S);
            // Set time to 0 for the next inner_procedure circle
            deadline -= time;           // Shift 2 * S.d amount in time
            time = 0;
            continue;
        }

        //cout << "Processing the event" << endl;

        // Process the event
        int machine = (*(S.Q.begin())).second; // Record the machine index 
        processEvent (S);

        // Machine becomes idle at time
        int jobIndex = getJob (machine, S);
        S.process (jobIndex, machine, time); // If jobIdex == -1, the machine becomes idle
    }

    S.TOTAL_MAKESPAN += min (time, deadline);
    return true;
}

/* Online Scheduling with a Known / Unknown Error */
int getJob (int i, const Status& S) 
{
    set<pair<double, int>>::iterator it1 = findJob (i, S, S.waitingJobs);
    set<pair<double, int>>::iterator it2 = findJob (i, S, S.largeProcessingJobs);

    if(i <= S.sup){ // [special case] The case only for fast machine (i <= sup)
        set<pair<double, int>>::iterator it3 = findJob (i, S, S.slowMachineJobs);
        if(it3 != S.slowMachineJobs.end() && (it1 == S.waitingJobs.end() || (*it3).first >= (*it1).first) 
            && (it2 == S.largeProcessingJobs.end() || (*it3).first >= (*it2).first)){
            return (*it3).second;
        }
    }

    // If it is not the special case
    return getJobIndex (it1, it2, S);
}

/* Online Classic Scheduling */
double Online_ClassicMakespan (Problem& instance)
{
    // Adpat the transformation to the problem: instance -> prob
    Problem prob = instance;
    for (int i = 0; i < prob.m; i++) {
        int k = log2(prob.speed[i]);
        prob.speed[i] = (1 << k);
    }
    
    Status S (&prob);
    S.init_Status ();
    S.I->m = S.m = S.sup + 1;
    prob.speed.erase(prob.speed.begin() + S.m, prob.speed.end());

    // Init eJobSize by setting p^e_j = 1
    for (int j = 0; j < S.n; j++) S.eJobSize[j] = 1.0;

    for (int j = 0; j < instance.n; j++) {
        // A new job is released
        double deadline = processJobRelease (S, j);
        // Find the makespan for the current stage
        S.d = S.max_jobSizeEstimate () / S.I->speed[0];
        Online_ClassicProcedure (S, deadline);
    }

    if (!S.ifValidComputed()) {
        cout << "BAD SCHEDULE!" << endl;
        exit(1);
    }

    return S.TOTAL_MAKESPAN;
}

// Online Classic Scheduling Procedure for processing one stage
bool Online_ClassicProcedure (Status& S, double deadline)
{
    // Initialize the event Q to keep cope with the current status
    reInitializeEventQOnlineClassic (S);
    // Process events
    double time = 0;
    while (true) {

        if ((!S.Q.empty() && (*(S.Q.begin())).first > deadline)) return false; // Time passes deadline
        if (S.Q.empty() && !S.hasActiveJobs()) break; // All active jobs are completed and the procedure returns
        if (S.Q.empty() || (!S.Q.empty() && (*(S.Q.begin())).first > 2 * S.d)) {
            /* Termination of this run */
            time = 2 * S.d;             // The current time is 2 * S.d
            bool impossible = S.impossibleToComplete();

            pauseRunning (S, time);     // Pause and shift timing variables and prepare the next stage processing
            // Initialize eJobSize or S.d and Q for the next stage
            if (impossible) {
                S.d = 2 * S.d;
            } else {
                for (const pair<double, int>& job: S.waitingJobs) {
                    int jobToUpdate = job.second;
                    int machineIndex = S.assigned[jobToUpdate];
                    S.eJobSize[jobToUpdate] = 2.0 * S.eJobSize[jobToUpdate];
                }
                S.updateJobSizeEstimates ();
            }
            // Initialize the event Q to keep cope with the current status
            reInitializeEventQOnlineClassic (S);
            // Set time to 0 for the next inner_procedure circle
            deadline -= time;           // Shift 2 * S.d amount in time
            time = 0;
            continue;
        }

        double curTime = (*(S.Q.begin())).first; 
        time = max (time, curTime);

        // Process the event
        int machine = (*(S.Q.begin())).second; // Record the machine index 
        processEvent (S);

        // Machine becomes idle at time
        int jobIndex = getJobClassic (machine, S);
        S.process (jobIndex, machine, time); // If jobIdex == -1, the machine becomes idle
    }

    S.TOTAL_MAKESPAN += min (time, deadline);
    return true;
}

// Return the index of the next job that will be processed on machine i for the classic online scheduling
int getJobClassic (int i, const Status& S)
{
    set<pair<double, int>>::iterator it1 = findJob (i, S, S.waitingJobs);
    if (it1 != S.waitingJobs.end()) {
        return (*it1).second;
    } else {
        return -1;
    }
}

// Offline Binary Search for the 3 relaxed makespan 
double OfflineRelaxedMakespan(Problem& instance)
{
    Status S (&instance);
    S.init_Status ();

    // Init eJobSize
    for (int j = 0; j < S.n; j++) S.eJobSize[j] = S.I->jobSize[j];

    for (int j = 0; j < instance.n; j++) {
        // A new job is released
        double deadline = processJobRelease (S, j);
        // Find the optimal makespan for the current stage
        S.d = Offline_BisectionSearch (S);
        Improved2_RelaxedProcedure (S, deadline);
    }

    if (!S.ifValidComputed()) {
        cout << "BAD SCHEDULE!" << endl;
        exit(1);
    }

    return S.TOTAL_MAKESPAN;
}

// Relaxed Offline Procedure for processing one stage
bool Improved2_RelaxedProcedure (Status& S, double deadline)
{
    // Initialize the event Q to keep cope with the current status
    reInitializeEventQOffline (S);

    // Process events
    double time = 0;
    while (!S.Q.empty()) {
        double curTime = (*(S.Q.begin())).first; 
        time = max (time, curTime);
        if (time > deadline) {
            return false; // the procedure fails to complete with all job finishes by deadline
        }

        // Process the event
        int machine = (*(S.Q.begin())).second; // Record the machine index 
        processEvent (S);

        // Machine becomes idle at time
        int jobIndex = getJob_improved2_Relaxed (machine, S);
        S.process (jobIndex, machine, time); // If jobIdex == -1, the machine becomes idle
    }

    S.TOTAL_MAKESPAN += min (time, deadline);
    return true;
}

// Return the optimal makespan for the status at the present time
double Offline_BisectionSearch (const Status& status)
{
    const double epsilon = 0.1;
    // Compute d_min, d_max
    double total_size = 0;
    Status S = status;
    // Compute d_max as the sum of the existing jobs / max speed
    for (const pair<double, int>& job: S.waitingJobs) total_size += job.first;
    double d_min = 0, d_max = total_size/S.I->speed[0];

    // Binary Search
    double opt_makespan = d_max;
    while(d_max - d_min > epsilon){
        double d_mid = d_min + (d_max - d_min)/2;
        S = status; S.d = d_mid; // a deep copy of the status object
        bool found = Improved2_RelaxedProcedure (S, 2 * S.d);
        if(found){
            opt_makespan = min(opt_makespan, d_mid);
            d_max = d_mid;
        }else{
            d_min = d_mid;
        }
    }

    return opt_makespan;
}

// Return the index of the next job that will be processed on machine i for the Offline Approximation solution
int getJob_improved2_Relaxed (int i, const Status& S)
{
    set<pair<double, int>>::iterator it1 = findJob (i, S, S.waitingJobs);
    set<pair<double, int>>::iterator it2 = findJob (i, S, S.largeProcessingJobs);

    return getJobIndex (it1, it2, S);
}

/* Common Subroutines */
double processJobRelease (Status& S, int j)
{
    // Process the Status to keep cope with the new job (J_j) release
    // The function returns the new deadline for the next stage processing
    S.TOTAL_MAKESPAN = S.I->releaseTime[j];
    double to_shift = S.I->releaseTime[j] - S.base_time;
    S.shift_Status (to_shift);
    S.validStatus (); // For validation only
    S.preemptJobs ();
    S.waitingJobs.insert(make_pair(S.eJobSize[j], j));
    double deadline;
    if (j < S.n - 1) deadline = S.I->releaseTime[j+1] - S.I->releaseTime[j];
    else deadline = INFINITY;

    return deadline;
}

void processEvent (Status& S)
{
    // Process the next event object
    int machine = (*(S.Q.begin())).second;
    S.Q.erase(S.Q.begin());
    int jobCompleted = S.processing[machine];

    if (jobCompleted >= 0) {
        S.completeJob (jobCompleted);
        S.freeMachine (machine);
    } // otherwise the machine is idle with S.processing[machine] == -1
}

// Find from jobSet the largest job with size <= si * d
set<pair<double, int>>::iterator findJob (int i, const Status& S, const set<pair<double, int>>& jobSet) 
{
    double si = ((S.I)->speed)[i];
    set<pair<double, int>>::iterator it = jobSet.upper_bound(make_pair(si * S.d, S.n + 1));
    if (it != jobSet.begin()) it--; else it = jobSet.end();

    return it;
}

// Return the job index using the iterators
int getJobIndex (const set<pair<double, int>>::iterator& it1, const set<pair<double, int>>::iterator& it2, const Status& S) 
{
    if(it1 != S.waitingJobs.end() && (it2 == S.largeProcessingJobs.end() || (*it1).first >= (*it2).first)){
        // choose a job from waitingJobs
        return (*it1).second;
    }else if(it2 != S.largeProcessingJobs.end() && (it1 == S.waitingJobs.end() || (*it1).first <= (*it2).first)){
        // choose a job from largeProcessingJobs
        return (*it2).second;
    }else{
        // The last case
        if(!S.waitingJobs.empty()){
            // Find the smallest waiting job to process
            set<pair<double, int>>::iterator it = S.waitingJobs.begin();
            return (*it).second;
        } // Otherwise the machine becomes idle return -1
    }
    return -1; // machine becomes idle
}

// Re-Initialize the Event Queue at the beginning of each stage of a procedure (For Offline Algorithms)
void reInitializeEventQOffline (Status& S)
{
    // Initialize the event Q to keep cope with the current status
    for (int i = 0; i < S.m; i++) {
        int jobIndex = getJob_improved2_Relaxed (i, S);
        S.init_process (jobIndex, i, 0);
    }
}

// Re-Initialize the Event Queue at the beginning of each stage of a procedure (For Online Algorithms)
void reInitializeEventQOnline (Status& S)
{
    // Initialize the event Q to keep cope with the current status
    for (int i = 0; i < S.m; i++) {
        int jobIndex = getJob (i, S);
        S.init_process (jobIndex, i, 0);
    }
}

// Re-Initialize the Event Queue at the beginning of each stage of a procedure (For Online Classic Algorithms)
void reInitializeEventQOnlineClassic (Status& S)
{
    // Initialize the event Q to keep cope with the current status
    for (int i = 0; i < S.m; i++) {
        int jobIndex = getJobClassic (i, S);
        S.init_process (jobIndex, i, 0);
    }
}

// Pause the running and shift the timing variables to update S.d and prepare for the next stage run
void pauseRunning (Status& S, double time)
{
    // Update S.d by doubling it and continue the processing
    // Shift 2 * S.d amount 
    S.shift_Status (time);      // Shift 2 * S.d amount in time
    S.validStatus ();           // For validation only
    S.TOTAL_MAKESPAN += time;   // Add the time to total_makespan
    S.preemptJobs ();
}

/* Random associated procedures */
void randProblem(Problem& instance, int m, int n)
{
    uniform_real_distribution<double> job_range(1, MAX_JOB_SIZE);
    uniform_real_distribution<double> release_range(0, MAX_RELEASE_TIME);
    uniform_real_distribution<double> speed_range(1, MAX_SPEED);

    instance.m = m, instance.n = n;
    instance.jobSize = vector<double>(n);
    instance.releaseTime = vector<double>(n);
    instance.speed = vector<double>(m);

    for(int j = 0; j < n; j++){
        instance.jobSize[j] = job_range(eng);
        instance.releaseTime[j] = release_range(eng);
    }
    for(int i = 0; i < m; i++){
        instance.speed[i] = speed_range(eng);
    }
    // Sort the machine speed in decreasing order
    sort(instance.speed.begin(), instance.speed.end(), greater<double>());
    // Sort the release time in increasing order
    sort(instance.releaseTime.begin(), instance.releaseTime.end());

    // Job size predictons
    instance.eta = 1;
    instance.jobSizePrediction = instance.jobSize;
}

void extendProblem(Problem& instance, int new_m)
{
    if(instance.m >= new_m) return ;

    instance.m = new_m;
    uniform_real_distribution<double> speed_range(1, MAX_SPEED);
    while(instance.speed.size() < new_m){
        instance.speed.push_back(speed_range(eng));
    }
    // Sort the machine speed in decreasing order
    sort(instance.speed.begin(), instance.speed.end(), greater<double>());
}

Problem loadProblem (const string& fileName)
{
    Problem prob;
    ifstream fin (fileName);
    fin >> prob.m >> prob.n >> prob.eta;
    prob.releaseTime = vector<double> (prob.n);
    prob.jobSize = vector<double> (prob.n);
    prob.speed = vector<double> (prob.m);
    prob.jobSizePrediction = vector<double> (prob.n);

    // Load release time and job size
    for (int j = 0; j < prob.n; j++) {
        string job; 
        fin >> job;
        job = job.substr(1, job.size()-2);
        int pos = job.find(",");
        double release_time = stod(job.substr(0, pos));
        double job_size = stod(job.substr(pos+1));
        prob.releaseTime[j] = release_time;
        prob.jobSize[j] = job_size;
    }
    // Load machine speed
    for (int i = 0; i < prob.m; i++) {
        double si;
        fin >> si;
        prob.speed[i] = si;
    }
    // Load job size predictions
    for (int j = 0; j < prob.n; j++) {
        double pj;
        fin >> pj;
        prob.jobSizePrediction[j] = pj;
    }

    fin.close();
    return prob;   
}

void predictSize(Problem& instance, double eta)
{
    instance.eta = eta;
    uniform_real_distribution<double> distance(1.0, eta);
    uniform_real_distribution<double> coin(0.0, 1.0);
    for(int j = 0; j < instance.n; j++){
        // The old methods for predicting job size:
        /*
        uniform_real_distribution<double> estimatedJobSize(max(1.0, instance.jobSize[j]/eta), instance.jobSize[j]*eta);
        instance.jobSizePrediction[j] = estimatedJobSize(eng);
        */
        uniform_real_distribution<double> distance(1.0, eta);
        double amplifier = distance(eng);
        double side = coin(eng);
        if (side < 0.5) {
            instance.jobSizePrediction[j] = max(1.0, instance.jobSize[j] / amplifier);
        } else {
            instance.jobSizePrediction[j] = max(1.0, instance.jobSize[j] * amplifier);
        }
    }
}

/* Printing Procedures */
void printProblem(const Problem& instance)
{
    cout << "no. machines = " << instance.m << " no. jobs = " << instance.n << " prediction error = " << instance.eta << endl;
    cout << "Job: ";
    for(int j = 0; j < instance.n; j++) {
        cout << "(" << instance.releaseTime[j] << "," << instance.jobSize[j] << ") ";
    }
    cout << endl;
    cout << "Machine speeds: ";
    for(const double& s: instance.speed){
        cout << s << " ";
    }
    cout << endl;
    cout << "Job size predictions: ";
    for (const double& pj: instance.jobSizePrediction){
        cout << pj << " ";
    }
    cout << endl;
}

void print_set (const set<pair<double, int>>& to_visualize) {
    cout << "{ ";
    for (const pair<double, int>& j: to_visualize) {
        cout << "(" << j.first << ":" << j.second << ") ";
    }
    cout << "}";
}

void print_vector (const vector<double>& to_visualize) {
    cout << "{ ";
    for (int i = 0; i < to_visualize.size(); i++) {
        cout << "(" << i << "," << to_visualize[i] << ") ";
    }
    cout << "}";
}

void print_vector (const vector<int>& to_visualize) {
    cout << "{ ";
    for (int i = 0; i < to_visualize.size(); i++) {
        cout << "(" << i << "," << to_visualize[i] << ") ";
    }
    cout << "}";
}

void print_vector (const vector<bool>& to_visualize) {
    cout << "{ ";
    for (int i = 0; i < to_visualize.size(); i++) {
        cout << "(" << i << "," << to_visualize[i] << ") ";
    }
    cout << "}";
}

void print (const Status& S) {
    cout << "===================================" << endl;
    cout << "m = " << S.m << " n = " << S.n << endl;
    cout << "-----------------------------------" << endl;
    cout << "Execution Parameters: " << endl;
    cout << "waitingJobs: "; print_set (S.waitingJobs); cout << endl;
    cout << "slowMachineJobs: "; print_set (S.slowMachineJobs); cout << endl;
    cout << "largeProcessingJobs: "; print_set (S.largeProcessingJobs); cout << endl;
    cout << "-----------------------------------" << endl;
    cout << "State Parameters: " << endl;
    cout << "release_time: "; print_vector (S.I->releaseTime); cout << endl;
    cout << "eJobSize: "; print_vector (S.eJobSize); cout << endl;
    cout << "assigned: "; print_vector (S.assigned); cout << endl;
    cout << "processing: "; print_vector (S.processing); cout << endl;
    cout << "complete_time: "; print_vector (S.complete_time); cout << endl;
    cout << "completed_job: "; print_vector (S.completed_job); cout << endl;
    cout << "===================================" << endl;
}

/* Total test function */
void test ()
{
    int repetitions = 10;
    int num_machine = (1 << 4);
    int num_job = (1 << 7);
    double prediction_error = (1 << 1);

    for (int run_id = 0; run_id < repetitions; run_id++) {
        Problem prob;
        randProblem (prob, num_machine, num_job);
        predictSize (prob, prediction_error);
        cout << "Processing the problem " << (run_id+1) << "/" << repetitions << endl;
        /*
        int n = prob.n;
        for (int j = 0; j < n; j++) prob.releaseTime[j] = 0;
        */
        //printProblem (prob);
        double online_unknow_error_makespan = Online_UnknownErrorMakespan (prob);
        double online_know_error_makespan = Online_KnownErrorMakespan (prob);
        double offline_makespan = OfflineRelaxedMakespan (prob);
        double online_classic = Online_ClassicMakespan (prob);
        double lower_bound_C_max = makespan_lowerbound (prob);

        cout << "Lower bound = " << lower_bound_C_max << endl;
        cout << "Offline approximation makespan = " << offline_makespan << endl;
        cout << "Online know error makespan = " << online_know_error_makespan << " (" << online_know_error_makespan/offline_makespan << ")" << endl;
        cout << "Online unknow error makespan = " << online_unknow_error_makespan << " (" << online_unknow_error_makespan/offline_makespan << ")" << endl;
        cout << "Online classic makespan = " << online_classic << " (" << online_classic/offline_makespan << ")" << endl;
    }
    cout << "ALL TESTS PASSED!" << endl;
}

double makespan_lowerbound (const Problem& prob)
{
    double total_size = 0, total_speed = 0;
    for(int i = 0; i < prob.m; i++){
        total_speed += prob.speed[i];
    }
    for(int j = 0; j < prob.n; j++){
        total_size += prob.jobSize[j];
    }
    double lower_bound_C_max = max(total_size/total_speed, prob.releaseTime.back());
    return lower_bound_C_max;
}

void test_OnlineUnknownErrorMakespan ()
{
    test_Algorithm (Online_UnknownErrorMakespan);
}

void test_OnlineKnownErrorMakespan ()
{
    test_Algorithm (Online_KnownErrorMakespan);
}

void test_OfflineRelaxedMakespan ()
{
    test_Algorithm (OfflineRelaxedMakespan);
}

void test_OnlineClassicMakespan ()
{
    test_Algorithm (Online_ClassicMakespan);
}

void test_all ()
{
    test_OfflineRelaxedMakespan ();
    test_OnlineKnownErrorMakespan ();
    test_OnlineUnknownErrorMakespan ();
    test_OnlineClassicMakespan ();
}

void test_Algorithm (double (*algo)(Problem& prob))
{
    const int k = 3;
    int num_machines[k] = {(1 << 1), (1 << 3), (1 << 6)};
    int num_jobs[k] = {(1 << 2), (1 << 5), (1 << 8)};
    double errors[k] = {(1 << 0), (1 << 3), INFINITY};

    int repetitions = 1000;

    for (int m_id = 0; m_id < k; m_id++) {
        for (int n_id = 0; n_id < k; n_id++) {
            int m = num_machines[m_id], n = num_jobs[n_id];
            for (int run_id = 0; run_id < repetitions; run_id++) {
                Problem prob;
                randProblem(prob, m, n);
                int prob_id = m_id * k * repetitions + (n_id * repetitions) + run_id + 1;
                cout << "Processing the problem " << prob_id << "/" << k * k * repetitions << endl;

                // Static Scheduling
                for (int error_id = 0; error_id < k; error_id++) {
                    double prediction_error = errors[error_id];
                    predictSize (prob, prediction_error);
                    double output_makespan = algo(prob);
                    double lower_bound_C_max = makespan_lowerbound(prob);
                    if (lower_bound_C_max > output_makespan) {
                        cerr << "lower_bound_C_max > output_makespan" << endl;
                        exit(1);
                    }
                }
                
                // Dynamic Scheduling
                for (int j = 0; j < n; j++) prob.releaseTime[j] = 0;
                for (int error_id = 0; error_id < k; error_id++) {
                    double prediction_error = errors[error_id];
                    predictSize (prob, prediction_error);
                    double output_makespan = algo(prob);
                    double lower_bound_C_max = makespan_lowerbound(prob);
                    if (lower_bound_C_max > output_makespan) {
                        cerr << "lower_bound_C_max > output_makespan" << endl;
                        exit(1);
                    }
                }
            }
        }
    }
    cout << "ALL TESTS PASSED!" << endl;
}

void debug_problem ()
{
    Problem prob = loadProblem ("the_job.txt");

    double t_online_know_error = Online_KnownErrorMakespan(prob);
}