/*
    This is the source code for ICAPS algorithms 
        4 algorithms to implement:
    (1) The improved 2-relaxed procedure as the performance baseline
    (2) The classic O(\log m)-competitive procedure
    (3) The online scheduling with known error
    (4) The online scheduling with unknon error
*/
#include <iostream>
#include <random>
#include <vector>
#include <set>
#include <queue>
#include <algorithm>
#include <iomanip>

using namespace std;

/* Constants */
const int N = 10000; // number of jobs
const double MAX_JOB_SIZE = 1000;
const double MAX_SPEED = 1000;
const int RAND_SEED = time(0);

/* Global Variable */
default_random_engine eng(RAND_SEED);

/* Declare a problem instance */
struct Problem{
    int n;  // n: number of jobs
    int m;  // m: number of machines

    vector<double> jobSize;     // of size n
    vector<double> releaseTime; // of size n 
    vector<double> speed;       // of size m

    /* Estimated size */
    double eta;
    vector<double> estimatedSize; // of size n
};


/* Procedure Declaration */

/* Offline Improved 2-relaxed procedure */
bool Improved2_Relaxed(const Problem& instance, double d, double& o_makespan);
double Offline2_RelaxedMakespan(const Problem& instance);

/* Online Scheduling Knowing the Error */
double OnlineKnowingError(const Problem& instance);
int getJob( const int i, const int sup, const double d, const int n, const vector<double>& speed, 
            const set<pair<double, int>>& waitingJobs, const set<pair<double, int>>& slowMachineJobs, const set<pair<double, int>>& largeProcessingJobs);

/* Online Scheduling Unknowing the Error */
double OnlineUnknowingError(const Problem& instance);

/* Classic Online Scheduling Procedures */
double OnlineClassic(const Problem& instance);

/* Problem associated procedures */
void randProblem(Problem& instance, int m, int n);
void extendProblem(Problem& instance, int new_m);
void predictSize(Problem& instance, double eta);
void printProblem(const Problem& instance);

/* Experimental Code */
void simulate(int num_instance, int num_repeat);

/* Test Functions */
void test();


int main()
{
    //cout << "random seed = " << RAND_SEED << endl;
    //test();
    simulate(3, 1);

    return 0;
}

/* Procedure Implementation */

/* Experimental Code */
void simulate(int num_instance, int num_repeat)
{
    const int num_eta = 8;
    const int max_log_m = 10;
    double etas[num_eta] = {1, 2, 4, 8, 16, 32, 64, MAX_JOB_SIZE*100.0}; 

    // ratios[eta][log_m][i]:
    //   i = 0: online_know_error
    //   i = 1: online_unknow_error
    //   i = 2: online_classic
    double ratios[num_eta][max_log_m+1][3];
    for(int k_eta = 0; k_eta < num_eta; k_eta++){
        for(int log_m = 1; log_m <= max_log_m; log_m++){
            for(int k = 0; k < 3; k++){
                ratios[k_eta][log_m][k] = 0;
            }
        }
    }

    int total_problem_instances = 0;
    for(int num_jobs = N/10; num_jobs <= N; num_jobs += N/10){ // For each number of jobs.
        for(int instance_id = 0; instance_id < num_instance; instance_id++){  // Generate num_instance number of problem instances
            total_problem_instances++;
            // Generate an instance
            Problem instance;
            randProblem(instance, 2, num_jobs);
            for(int log_m = 1; log_m <= max_log_m; log_m += 1){   // log of number of machines
                int m = (1 << log_m);
                extendProblem(instance, m);
                double opt_makespan = Offline2_RelaxedMakespan(instance);
                double online_classic = OnlineClassic(instance);

                for(int k_eta = 0; k_eta < num_eta; k_eta++){
                    double eta = etas[k_eta];
                    double online_know_error = 0, online_unknow_error = 0;
                    // Repeat num_repeat times
                    for(int repeat_id = 0; repeat_id < num_repeat; repeat_id++){
                        predictSize(instance, eta);
                        // Solve instance two times
                        online_know_error += OnlineKnowingError(instance);
                        online_unknow_error += OnlineUnknowingError(instance);
                    }
                    online_know_error /= num_repeat; online_unknow_error /= num_repeat;

                    // no. jobs = num_jobs, no. machines = m, error = eta
                    /* Compute competitive ratio(s) */
                    double online_classic_ratio = online_classic / opt_makespan;
                    double online_know_ratio = online_know_error / opt_makespan;
                    double online_unknow_ratio = online_unknow_error / opt_makespan;

                    ratios[k_eta][log_m][0] += online_know_ratio;
                    ratios[k_eta][log_m][1] += online_unknow_ratio;
                    ratios[k_eta][log_m][2] += online_classic_ratio;
                }
            }
        }
    }

    for(int k_eta = 0; k_eta < num_eta; k_eta++){
        for(int log_m = 1; log_m <= max_log_m; log_m += 1){
            for(int k = 0; k < 3; k++){
                ratios[k_eta][log_m][k] /= total_problem_instances;
            }
        }
    }

    // Output the experimental data
    for(int k_eta = 0; k_eta < num_eta; k_eta++){
        cout << "eta = " << ((k_eta < num_eta-1)? to_string(etas[k_eta]):"inf") << ":" << endl;
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


/* Total test function */
void test()
{
    Problem prob;
    randProblem(prob, (1 << 20), (1 << 20));

    double o_makespan = Offline2_RelaxedMakespan(prob);

    double total_size = 0, total_speed = 0;
    for(int i = 0; i < prob.m; i++){
        total_speed += prob.speed[i];
    }
    for(int j = 0; j < prob.n; j++){
        total_size += prob.jobSize[j];
    }
    double lower_bound_C_max = total_size/total_speed;

    cout << "Lower bound = " << lower_bound_C_max << endl;
    cout << "optimal makespan = " << o_makespan << endl;

    double eta = 1; double makespan;
    for(int repeat = 0; repeat < 7; repeat++){
        predictSize(prob, eta);
        makespan = OnlineKnowingError(prob);
        cout << "KNOWN eta = " << setw(2) << eta << ":  makespan = " << setprecision(5) << makespan << "  competitive ratio = " << setprecision(3) << makespan/o_makespan << endl;
        makespan = OnlineUnknowingError(prob);
        cout << "UNKNOWN:\t makespan = "  << setprecision(5) << makespan << "  competitive ratio = " << setprecision(3) << makespan/o_makespan << endl;
        makespan = OnlineClassic(prob);
        cout << "CLASSIC:\t makespan = "  << setprecision(5) << makespan << "  competitive ratio = " << setprecision(3) << makespan/o_makespan << endl;
        cout << endl;
        eta *= 2;
    }
}

/* Online Scheduling Unknowing the Error */
double OnlineUnknowingError(const Problem& instance)
{
    /* Stage 1: Determine sup */
    double totalSpeed = 0;
    for(const double& s: instance.speed) totalSpeed += s;
    int sup = -1; double curTotalSpeed = 0;
    while(curTotalSpeed < 0.5 * totalSpeed){
        sup++;
        curTotalSpeed += instance.speed[sup];
    }

    /* Stage 2: Pre-process all jobs with estimated job size */
    /* Unpacking all the variables */
    int m = instance.m, n = instance.n;
    double eta = 1; // This is error estimate
    vector<double> eJobSize(n, 0);
    for(int j = 0; j < n; j++){
        eJobSize[j] = max(1.0, instance.estimatedSize[j]/eta);
    }

    // Set of jobs not begin
    set<pair<double, int>> waitingJobs;
    // Set of jobs begin at slow machines (i > sup)
    set<pair<double, int>> slowMachineJobs;
    // Set of jobs begin at some machine not fast enough
    set<pair<double, int>> largeProcessingJobs;

    // Initialize waitingJobs
    for(int j = 0; j < n; j++){
        waitingJobs.insert(make_pair(eJobSize[j], j));
    }

    /* Begin scheduling simulation */
    vector<int> assigned(n, -1);
    vector<double> complete_time(m, 0);
    vector<int> processing(m, -1);
    vector<bool> completed_job(n, false);

    double d = 0;
    for(int j = 0; j < n; j++) d = max(d, eJobSize[j]);
    d /= instance.speed[0];

    double TOTAL_MAKESPAN = 0;
    int num_completed_jobs = 0;
    
    /* Run the Core loop */
    // An event queue (time, machine_id)
    set<pair<double, int>> Q;
    while(num_completed_jobs < n){
        // Run the improved 2 relaxed procedure
        double time = 0;
        if(num_completed_jobs == n) break;

        /* Stage 3: Initially assign & adjust jobs to each machine */
        for(int i = 0; i < m; i++){
            int jobIndex = getJob(i, sup, d, n, instance.speed, waitingJobs, slowMachineJobs, largeProcessingJobs);
            // idle the current machine unless it is processing the job it should process...
            if(processing[i] >= 0 && processing[i] != jobIndex){
                Q.erase(make_pair(complete_time[i], i));
                waitingJobs.insert(make_pair(eJobSize[processing[i]], processing[i]));
                assigned[processing[i]] = -1;
                processing[i] = -1;
            }
            if(processing[i] == -1){ // If it is already idle and it is preparing for the next assignment
                Q.erase(make_pair(complete_time[i], i));
            }

            if(jobIndex == -1) continue; // The machine remains idle
            // Continue processing the job
            if(processing[i] == jobIndex){
                waitingJobs.erase(make_pair(eJobSize[jobIndex], jobIndex));
                // Maybe this job needs to go to slowMachineJobs or largeProcessingJobs
                if(instance.speed[i] * d < eJobSize[jobIndex]){
                    largeProcessingJobs.insert(make_pair(eJobSize[jobIndex], jobIndex));
                }else if(i > sup){
                    slowMachineJobs.insert(make_pair(eJobSize[jobIndex], jobIndex));
                }
                continue ;
            }
            // idle the machine currently processing jobIndex 
            int curMachine = assigned[jobIndex];
            if(curMachine >= 0){
                Q.erase(make_pair(complete_time[curMachine], curMachine));
                complete_time[curMachine] = 0;
                processing[curMachine] = -1;
            }
            // assign jobIndex to machine i
            double c_time = time + instance.jobSize[jobIndex]/instance.speed[i];
            assigned[jobIndex] = i;
            complete_time[i] = c_time; 
            processing[i] = jobIndex;
            Q.insert(make_pair(c_time, i));
            waitingJobs.erase(make_pair(eJobSize[jobIndex], jobIndex));

            if(instance.speed[i] * d < eJobSize[jobIndex]){
                largeProcessingJobs.insert(make_pair(eJobSize[jobIndex], jobIndex));
            }else if(i > sup){
                slowMachineJobs.insert(make_pair(eJobSize[jobIndex], jobIndex));
            }
        }

        bool underestimationError = false;
        /* Stage 4: Process events */
        while(!Q.empty()){
            double curTime = (*(Q.begin())).first;
            if(curTime > 2*d){
                /* Termination of this run */
                time = 2*d;
                break;
            }

            time = max(time, curTime);
            int machine = (*(Q.begin())).second;
            
            // Process the event: 
            Q.erase(Q.begin());
            // time <= 2*d, Scheduling! 
            if(curTime > 0){
                num_completed_jobs++;
                int c_job = processing[machine];

                completed_job[c_job] = true;
                slowMachineJobs.erase(make_pair(eJobSize[c_job], c_job));
                largeProcessingJobs.erase(make_pair(eJobSize[c_job], c_job));

                /* Determine if the error is underestimated */
                if(eJobSize[c_job]/eta > instance.jobSize[c_job]){
                    // machine is idle at time
                    processing[machine] = -1;
                    complete_time[machine] = 0;
                    underestimationError = true;
                    Q.insert(make_pair(complete_time[machine], machine));
                    break; // Break the processing events
                }
            }

            // machine is idle at time
            processing[machine] = -1;
            complete_time[machine] = 0;

            int jobIndex = getJob(machine, sup, d, n, instance.speed, waitingJobs, slowMachineJobs, largeProcessingJobs);

            if(jobIndex == -1) continue ; // Machine becomes idle

            /* machine processes jobIndex */

            // idle the machine current processing jobIdex
            if(assigned[jobIndex] >= 0){
                int idle_machine = assigned[jobIndex];
                // Idle the machine
                Q.erase(make_pair(complete_time[idle_machine], idle_machine));
                Q.insert(make_pair(0, idle_machine));
                complete_time[idle_machine] = 0;
                processing[idle_machine] = -1;
            }

            waitingJobs.erase(make_pair(eJobSize[jobIndex], jobIndex));
            slowMachineJobs.erase(make_pair(eJobSize[jobIndex], jobIndex));
            largeProcessingJobs.erase(make_pair(eJobSize[jobIndex], jobIndex));

            if(instance.speed[machine] * d < eJobSize[jobIndex]){
                largeProcessingJobs.insert(make_pair(eJobSize[jobIndex], jobIndex));
            }else if(machine > sup){
                slowMachineJobs.insert(make_pair(eJobSize[jobIndex], jobIndex));
            }

            double c_time = time + instance.jobSize[jobIndex]/instance.speed[machine];
            Q.insert(make_pair(c_time, machine));

            assigned[jobIndex] = machine; 
            complete_time[machine] = c_time;
            processing[machine] = jobIndex;
        }

        /* Stage 5: At the termination of a decision procedure */
        if(num_completed_jobs == n){
            // The whole schedule finishes
            TOTAL_MAKESPAN += time;
            return TOTAL_MAKESPAN;
        }
        // num_completed_jobs < n, then time is at 2*d
        TOTAL_MAKESPAN += min(2*d, time);

        // Decide if update eJobSize or d, or updating eta
        bool impossible = (!waitingJobs.empty() || !slowMachineJobs.empty() || !largeProcessingJobs.empty());
        if(!impossible){
            // Check all fast machines
            for(int i = 0; i <= sup; i++){
                if(processing[i] >= 0){
                    double startTime = complete_time[i] - instance.jobSize[processing[i]]/instance.speed[i];
                    if(startTime >= d){
                        impossible = true;
                        break;
                    }
                }
            }
        }

        /* Stage 6: Updates! */
        set<pair<double, int>> Q_updated;
        for(const pair<double, int>& event: Q){
            double n_complete_time = event.first - min(2*d, time); int machine = event.second;
            complete_time[machine] = max(0.0, n_complete_time);
            Q_updated.insert(make_pair(complete_time[machine], event.second));
        }
        Q = Q_updated;

        if(underestimationError && (eta)*(eta) < m){
            // underestimation of eta
            if((2*eta)*(2*eta) < m){
                eta = eta * 2;
                for(int j = 0; j < n; j++){
                    eJobSize[j] = instance.estimatedSize[j] / eta;
                }
            }else{
                eta = MAX_JOB_SIZE * 10;
                for(int j = 0; j < n; j++){
                    eJobSize[j] = 1; // the smallest job size
                }
            }
            // update (re-initialize) d 
            d = 0;
            for(int j = 0; j < n; j++) if(!completed_job[j]) d = max(d, eJobSize[j]);
            d /= instance.speed[0];
        }else if(impossible){
            // Update makespan estimate and break
            d = 2 * d;
        }else{
            // Update all estimated Job Size for unfinished jobs
            for(int i = 0; i <= sup; i++){
                if(processing[i] >= 0){
                    double startTime = complete_time[i] - instance.jobSize[processing[i]]/instance.speed[i];
                    eJobSize[processing[i]] = max(2 * eJobSize[processing[i]], 2 * instance.speed[i] * (2*d - startTime));
                }
            }
        }

        waitingJobs.clear();
        slowMachineJobs.clear();
        largeProcessingJobs.clear();
        for(int j = 0; j < n; j++){
            if(!completed_job[j]){
                waitingJobs.insert(make_pair(eJobSize[j], j));
            }
        }
    }

    return TOTAL_MAKESPAN;
}

/* Online Scheduling Knowing the Error */
double OnlineKnowingError(const Problem& instance)
{
    /* Stage 1: Determine sup */
    double totalSpeed = 0;
    for(const double& s: instance.speed) totalSpeed += s;
    int sup = -1; double curTotalSpeed = 0;
    while(curTotalSpeed < 0.5 * totalSpeed){
        sup++;
        curTotalSpeed += instance.speed[sup];
    }

    /* Stage 2: Pre-process all jobs with estimated job size */
    /* Unpacking all the variables */
    int m = instance.m, n = instance.n;
    double eta = instance.eta;
    vector<double> eJobSize(n, 0);
    for(int j = 0; j < n; j++){
        eJobSize[j] = max(1.0, instance.estimatedSize[j]/eta);
    }

    // Set of jobs not begin
    set<pair<double, int>> waitingJobs;
    // Set of jobs begin at slow machines (i > sup)
    set<pair<double, int>> slowMachineJobs;
    // Set of jobs begin at some machine not fast enough
    set<pair<double, int>> largeProcessingJobs;

    // Initialize waitingJobs
    for(int j = 0; j < n; j++){
        waitingJobs.insert(make_pair(eJobSize[j], j));
    }

    /* Begin scheduling simulation */
    vector<int> assigned(n, -1);
    vector<double> complete_time(m, 0);
    vector<int> processing(m, -1);
    vector<bool> completed_job(n, false);

    double d = 0;
    for(int j = 0; j < n; j++) d = max(d, eJobSize[j]);
    d /= instance.speed[0];

    double TOTAL_MAKESPAN = 0;
    int num_completed_jobs = 0;
    
    /* Run the Core loop */
    // An event queue (time, machine_id)
    set<pair<double, int>> Q;

    while(num_completed_jobs < n){
        // Run the improved 2 relaxed procedure
        double time = 0;
        if(num_completed_jobs == n) break;

        /* Stage 3: Initially assign & adjust jobs to each machine */
        for(int i = 0; i < m; i++){
            int jobIndex = getJob(i, sup, d, n, instance.speed, waitingJobs, slowMachineJobs, largeProcessingJobs);

            // idle the current machine unless it is processing the job it should process...
            if(processing[i] >= 0 && processing[i] != jobIndex){
                Q.erase(make_pair(complete_time[i], i));
                waitingJobs.insert(make_pair(eJobSize[processing[i]], processing[i]));
                assigned[processing[i]] = -1;
                processing[i] = -1;
            }
            if(processing[i] == -1){ // If it is already idle and it is preparing for the next assignment
                Q.erase(make_pair(complete_time[i], i));
            }

            if(jobIndex == -1) continue; // The machine remains idle
            // Continue processing the job
            if(processing[i] == jobIndex){
                waitingJobs.erase(make_pair(eJobSize[jobIndex], jobIndex));
                // Maybe this job needs to go to slowMachineJobs or largeProcessingJobs
                if(instance.speed[i] * d < eJobSize[jobIndex]){
                    largeProcessingJobs.insert(make_pair(eJobSize[jobIndex], jobIndex));
                }else if(i > sup){
                    slowMachineJobs.insert(make_pair(eJobSize[jobIndex], jobIndex));
                }

                continue ;
            }
            // idle the machine currently processing jobIndex 
            int curMachine = assigned[jobIndex];
            if(curMachine >= 0){
                Q.erase(make_pair(complete_time[curMachine], curMachine));
                complete_time[curMachine] = 0;
                processing[curMachine] = -1;
            }
            // assign jobIndex to machine i
            double c_time = time + instance.jobSize[jobIndex]/instance.speed[i];
            assigned[jobIndex] = i;
            complete_time[i] = c_time; 
            processing[i] = jobIndex;
            Q.insert(make_pair(c_time, i));
            waitingJobs.erase(make_pair(eJobSize[jobIndex], jobIndex));

            if(instance.speed[i] * d < eJobSize[jobIndex]){
                largeProcessingJobs.insert(make_pair(eJobSize[jobIndex], jobIndex));
            }else if(i > sup){
                slowMachineJobs.insert(make_pair(eJobSize[jobIndex], jobIndex));
            }
        }

        /* Stage 4: Process events */
        while(!Q.empty()){
            double curTime = (*(Q.begin())).first;
            if(curTime > 2*d){
                /* Termination of this run */
                time = 2*d;
                break;
            }
            time = max(time, curTime);
            int machine = (*(Q.begin())).second;
            
            // Process the event: 
            Q.erase(Q.begin());

            // time <= 2*d, Scheduling! 
            if(curTime > 0){
                num_completed_jobs++;
                int c_job = processing[machine];
                completed_job[c_job] = true;
                slowMachineJobs.erase(make_pair(eJobSize[c_job], c_job));
                largeProcessingJobs.erase(make_pair(eJobSize[c_job], c_job));
            }

            // machine is idle at time
            processing[machine] = -1;
            complete_time[machine] = 0;

            int jobIndex = getJob(machine, sup, d, n, instance.speed, waitingJobs, slowMachineJobs, largeProcessingJobs);

            if(jobIndex == -1) continue ; // Machine becomes idle

            /* machine processes jobIndex */

            // idle the machine current processing jobIdex
            if(assigned[jobIndex] >= 0){
                int idle_machine = assigned[jobIndex];
                // Idle the machine
                Q.erase(make_pair(complete_time[idle_machine], idle_machine));
                Q.insert(make_pair(0, idle_machine));
                complete_time[idle_machine] = 0;
                processing[idle_machine] = -1;
            }

            waitingJobs.erase(make_pair(eJobSize[jobIndex], jobIndex));
            slowMachineJobs.erase(make_pair(eJobSize[jobIndex], jobIndex));
            largeProcessingJobs.erase(make_pair(eJobSize[jobIndex], jobIndex));

            if(instance.speed[machine] * d < eJobSize[jobIndex]){
                largeProcessingJobs.insert(make_pair(eJobSize[jobIndex], jobIndex));
            }else if(machine > sup){
                slowMachineJobs.insert(make_pair(eJobSize[jobIndex], jobIndex));
            }

            double c_time = time + instance.jobSize[jobIndex]/instance.speed[machine];
            Q.insert(make_pair(c_time, machine));
            assigned[jobIndex] = machine; 
            complete_time[machine] = c_time;
            processing[machine] = jobIndex;
        }

        /* Stage 5: At the termination of a decision procedure */
        if(num_completed_jobs == n){
            // The whole schedule finishes
            TOTAL_MAKESPAN += time;
            return TOTAL_MAKESPAN;
        }
        // num_completed_jobs < n, then time is at 2*d
        TOTAL_MAKESPAN += min(2*d, time);

        // Decide if update eJobSize or d
        bool impossible = (!waitingJobs.empty() || !slowMachineJobs.empty() || !largeProcessingJobs.empty());
        if(!impossible){
            // Check all fast machines
            for(int i = 0; i <= sup; i++){
                if(processing[i] >= 0){
                    double startTime = complete_time[i] - instance.jobSize[processing[i]]/instance.speed[i];
                    if(startTime >= d || (i == 0 && startTime < d)){
                        impossible = true;
                        break;
                    }
                }
            }
        }

        /* Stage 6: Updates! */
        set<pair<double, int>> Q_updated;
        for(const pair<double, int>& event: Q){
            double n_complete_time = event.first - 2*d; int machine = event.second;
            complete_time[machine] = max(0.0, n_complete_time);
            Q_updated.insert(make_pair(complete_time[machine], event.second));
        }
        Q = Q_updated;

        if(impossible){
            // Update makespan estimate and break
            d = 2 * d;
        }else{
            // Update all estimated Job Size for unfinished jobs
            for(int i = 0; i <= sup; i++){
                if(processing[i] >= 0){
                    double startTime = complete_time[i] - instance.jobSize[processing[i]]/instance.speed[i];
                    eJobSize[processing[i]] = max(2 * eJobSize[processing[i]], 2 * instance.speed[i] * (2*d - startTime));
                }
            }
        }

        waitingJobs.clear();
        slowMachineJobs.clear();
        largeProcessingJobs.clear();
        for(int j = 0; j < n; j++){
            if(!completed_job[j]){
                waitingJobs.insert(make_pair(eJobSize[j], j));
            }
        }
    }

    return TOTAL_MAKESPAN;
}

int getJob( const int i, const int sup, const double d, const int n, const vector<double>& speed, 
            const set<pair<double, int>>& waitingJobs, const set<pair<double, int>>& slowMachineJobs, const set<pair<double, int>>& largeProcessingJobs)
{
    double si = speed[i];

    set<pair<double, int>>::iterator it1 = waitingJobs.upper_bound(make_pair(si*d, n+1));
    if(it1 != waitingJobs.begin()) it1--; else it1 = waitingJobs.end();

    set<pair<double, int>>::iterator it2 = largeProcessingJobs.upper_bound(make_pair(si*d, n+1));
    if(it2 != largeProcessingJobs.begin()) it2--; else it2 = largeProcessingJobs.end();

    if(i <= sup){ // [special case] The case only for fast machine (i <= sup)
        set<pair<double, int>>::iterator it3 = slowMachineJobs.upper_bound(make_pair(si*d, n+1));
        if(it3 != slowMachineJobs.begin()) it3--; else it3 = slowMachineJobs.end();
        if(it3 != slowMachineJobs.end() && (it1 == waitingJobs.end() || (*it3).first >= (*it1).first) && (it2 == largeProcessingJobs.end() || (*it3).first >= (*it2).first)){
            return (*it3).second;
        }
    }

    // If it is not the special case
    if(it1 != waitingJobs.end() && (it2 == largeProcessingJobs.end() || (*it1).first >= (*it2).first)){
        // choose a job from waitingJobs
        return (*it1).second;
    }else if(it2 != largeProcessingJobs.end() && (it1 == waitingJobs.end() || (*it1).first <= (*it2).first)){
        // choose a job from largeProcessingJobs
        return (*it2).second;
    }else{
        // The last case
        if(!waitingJobs.empty()){
            // Find the smallest waiting job to process
            set<pair<double, int>>::iterator it = waitingJobs.begin();
            return (*it).second;
        } // Otherwise the machine becomes idle return -1
    }
    return -1; // machine becomes idle
}

/* Offline Improved 2-relaxed procedures */

/* Binary Search for the 2 relaxed makespan */
double Offline2_RelaxedMakespan(const Problem& instance)
{
    // Compute d_min
    double total_size = 0, total_speed = 0;
    for(int j = 0; j < instance.n; j++){
        total_size += instance.jobSize[j];
    }
    for(int i = 0; i < instance.m; i++){
        total_speed += instance.speed[i];
    }

    double d_min = total_size/total_speed, d_max = total_size/instance.speed[0];
    double opt_makespan  = d_max;
    while(d_max - d_min > 0.001){
        double d_mid = d_min + (d_max - d_min)/2;
        double o_makespan;
        bool found = Improved2_Relaxed(instance, d_mid, o_makespan);
        if(found){
            opt_makespan = min(opt_makespan, o_makespan);
            d_max = d_mid;
        }else{
            d_min = d_mid;
        }
    }
    return opt_makespan;
}

/* The decision procedure */
bool Improved2_Relaxed(const Problem& instance, double d, double& o_makespan)
{
    /* A decision procedure that returns:
        true (construct a schedule of length <= 2d); 
        false (if the schedule cannot have length <= d)
    */
    int m = instance.m, n = instance.n;
    // Set of jobs not begin
    set<pair<double, int>> waitingJobs;
    // Set of jobs begin at some machine not fast enough
    set<pair<double, int>> largeProcessingJobs;

    // Initialize waitingJobs
    for(int j = 0; j < n; j++){
        waitingJobs.insert(make_pair(instance.jobSize[j], j));
    }

    /* Begin scheduling simulation */
    vector<int> assigned(n, -1);
    vector<double> complete_time(m, 0);
    vector<int> processing(m, -1);

    // An event queue (time, machine_id)
    set<pair<double, int>> Q;
    // Initial events
    for(int i = 0; i < m; i++){
        Q.insert(make_pair(0, i));
    }
    // Process events
    double time = 0;
    int num_completed_jobs = 0;
    while(!Q.empty()){
        double curTime = (*(Q.begin())).first;
        time = max(time, curTime);
        int machine = (*(Q.begin())).second;
        if(time > 2*d){
            o_makespan = time;
            return false;
        }
        // Process the event
        Q.erase(Q.begin());

        if(curTime > 0){
            num_completed_jobs++;
            // The job is erased if it is in largeProcessingJobs
            largeProcessingJobs.erase(make_pair(instance.jobSize[processing[machine]], processing[machine]));
        }

        // machine is idle at time
        double si = instance.speed[machine];
        set<pair<double, int>>::iterator it1 = waitingJobs.upper_bound(make_pair(si*d, n+1));
        if(it1 != waitingJobs.begin()) it1--; else it1 = waitingJobs.end();

        set<pair<double, int>>::iterator it2 = largeProcessingJobs.upper_bound(make_pair(si*d, n+1));
        if(it2 != largeProcessingJobs.begin()) it2--; else it2 = largeProcessingJobs.end();

        if(it1 != waitingJobs.end() && (it2 == largeProcessingJobs.end() || (*it1).first >= (*it2).first)){
            // choose a job from waitingJobs
            double jsize = (*it1).first; int jobIndex = (*it1).second;
            double ptime = jsize/si;
            double c_time = time + ptime;
            Q.insert(make_pair(c_time, machine));
            assigned[jobIndex] = machine; 
            complete_time[machine] = c_time;
            processing[machine] = jobIndex;
            waitingJobs.erase(it1);
        }else if(it2 != largeProcessingJobs.end() && (it1 == waitingJobs.end() || (*it1).first <= (*it2).first)){
            // choose a job from largeProcessingJobs
            double jsize = (*it2).first; int jobIndex = (*it2).second;
            double ptime = jsize/si;
            double c_time = time + ptime;
            Q.insert(make_pair(c_time, machine));

            // Remove the event of jobIndex being processed in Q
            int slow_machine = assigned[jobIndex]; double slow_ctime = complete_time[slow_machine];
            Q.erase(make_pair(slow_ctime, slow_machine));
            Q.insert(make_pair(0, slow_machine)); // assign some job to this machine next
            // Update the assigned and complete_time
            assigned[jobIndex] = machine;
            complete_time[machine] = c_time;
            processing[machine] = jobIndex;
            // Job is completed removed for processing
            largeProcessingJobs.erase(it2);
        }else{
            // The last case
            if(!waitingJobs.empty()){
                // Find the smallest waiting job to process
                set<pair<double, int>>::iterator it = waitingJobs.begin();
                double jsize = (*it).first; int jobIndex = (*it).second;
                double c_time = time + jsize/si;
                
                Q.insert(make_pair(c_time, machine));
                assigned[jobIndex] = machine;
                complete_time[machine] = c_time; 
                processing[machine] = jobIndex;

                largeProcessingJobs.insert(*it);
                waitingJobs.erase(it);
            } // Otherwise the machine becomes idle
        }
    }

    o_makespan = time;
    return num_completed_jobs == n;
}


/* Classic Online Scheduling Procedures */
double OnlineClassic(const Problem& instance)
{
    /* Stage 1: Pre-processing and Reduction */
    // Randomized job sizes: Use this for the entire algorithm
    vector<double> jobSize = instance.jobSize;
    shuffle(jobSize.begin(), jobSize.end(), eng);
    
    // Compute the actual machine speed:
    vector<double> speed = instance.speed;
    for(int i = 0; i < instance.m; i++){
        int k = log2(speed[i]);
        speed[i] = (1 << k);
    }
    // Compute sup, m, and n
    double totalSpeed = 0;
    for(const double& s: speed) totalSpeed += s;
    int sup = -1; double curTotalSpeed = 0;
    while(curTotalSpeed < 0.5 * totalSpeed){
        sup++;
        curTotalSpeed += speed[sup];
    }
    int m = sup + 1; int n = instance.n;

    speed.erase(speed.begin() + m, speed.end());

    /* Use speed (of size m), jobSize (of size n), sup, m, n to perform scheduling */

    /* Stage 2: Pre-process all jobs with estimated job size */
    /* Begin scheduling simulation */
    vector<int> assigned(n, -1);
    vector<double> complete_time(m, 0);
    vector<int> processing(m, -1);
    vector<bool> completed_job(n, false);

    /* Run job 0 to estimate d */
    double d = jobSize[0]/speed[0];
    completed_job[0] = true;

    vector<double> eJobSize(n, 0);
    for(int j = 0; j < n; j++){
        eJobSize[j] = d * speed[m-1];
    }
    // Set of jobs not begin
    set<pair<double, int>> waitingJobs;
    // Initialize waitingJobs (except for job 0)
    for(int j = 1; j < n; j++){
        waitingJobs.insert(make_pair(eJobSize[j], j));
    }

    double TOTAL_MAKESPAN = d;
    int num_completed_jobs = 1; 

    /* Stage 3: Run the Core loop */
    while(num_completed_jobs < n){
        // An event queue (time, machine_id)
        set<pair<double, int>> Q;
        double time = 0;

        // Initially all machines are idle
        for(int i = 0; i < m; i++){
            Q.insert(make_pair(0, i));
        }

        /* Stage 4: Process events */
        while(!Q.empty()){
            double curTime = (*(Q.begin())).first;
            time = max(time, curTime);
            int machine = (*(Q.begin())).second;

            if(time > 2*d){
                /* Termination of this run */
                break;
            }
            // Process the event: 
            Q.erase(Q.begin());

            if(curTime > 0){ // Complete a job
                num_completed_jobs++;
                int c_job = processing[machine];
                completed_job[c_job] = true;
            }   

            // machine is idle at time
            processing[machine] = -1;
            complete_time[machine] = 0;

            // Idle the machine if curTime < d
            if(curTime >= d) continue ;

            // curTime < d
            set<pair<double, int>>::iterator it = waitingJobs.upper_bound(make_pair(speed[machine]*d, n+1));
            int jobIndex;
            if(it == waitingJobs.begin()) jobIndex = -1;
            else{
                it--;
                jobIndex = (*it).second;
            }

            if(jobIndex == -1) continue ; // Machine becomes idle            

            /* machine processes jobIndex */
            waitingJobs.erase(make_pair(eJobSize[jobIndex], jobIndex));

            double c_time = time + jobSize[jobIndex]/speed[machine];
            Q.insert(make_pair(c_time, machine));
            assigned[jobIndex] = machine; 
            complete_time[machine] = c_time;
            processing[machine] = jobIndex;
        }

        /* Stage 5: At the termination of a decision procedure */
        if(num_completed_jobs == n){
            // The whole schedule finishes
            TOTAL_MAKESPAN += time;
            return TOTAL_MAKESPAN;
        }
        // num_completed_jobs < n, then time is at 2*d
        TOTAL_MAKESPAN += min(2*d, time);

        // Decide if update eJobSize or d
        bool double_d = false;
        for(int i = 0; i < m && speed[i] == speed[0]; i++){
            if(processing[i] >= 0){
                double_d = true;
                break;
            }
        }
        double_d = (double_d || !waitingJobs.empty());

        /* Stage 6: Updates! */
        Q.clear();

        if(double_d){
            // Update makespan estimate and break
            d = 2 * d;
            for(int j = 0; j < n; j++){
                if(!completed_job[j]){
                    eJobSize[j] = d * speed[m-1];
                }
            }
        }else{
            // Update all estimated Job Size for unfinished jobs
            for(int i = 0; i < m; i++){
                if(processing[i] >= 0){
                    eJobSize[processing[i]] = 2 * speed[i] * d;
                }
            }
        }

        waitingJobs.clear();
        for(int j = 0; j < n; j++){
            if(!completed_job[j]){
                waitingJobs.insert(make_pair(eJobSize[j], j));
            }
        }
    }

    return TOTAL_MAKESPAN;
}


/* Random associated procedures */
void randProblem(Problem& instance, int m, int n)
{
    uniform_real_distribution<double> job_range(1, MAX_JOB_SIZE);
    uniform_real_distribution<double> speed_range(1, MAX_SPEED);

    instance.m = m, instance.n = n;
    instance.jobSize = vector<double>(n);
    instance.speed = vector<double>(m);

    for(int j = 0; j < n; j++){
        instance.jobSize[j] = job_range(eng);
    }
    for(int i = 0; i < m; i++){
        instance.speed[i] = speed_range(eng);
    }
    // Sort both the job size and speed in decreasing order
    sort(instance.speed.begin(), instance.speed.end(), greater<double>());
    sort(instance.jobSize.begin(), instance.jobSize.end(), greater<double>());

    // Estimated job size
    instance.eta = 1;
    instance.estimatedSize = instance.jobSize;
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

void predictSize(Problem& instance, double eta)
{
    instance.eta = eta;
    for(int j = 0; j < instance.n; j++){
        uniform_real_distribution<double> estimatedJobSize(max(1.0, instance.jobSize[j]/eta), instance.jobSize[j]*eta);
        instance.estimatedSize[j] = estimatedJobSize(eng);
    }
}

void printProblem(const Problem& instance)
{
    cout << "no. machines = " << instance.m << " no. jobs = " << instance.n << endl;
    cout << "Job sizes: ";
    for(const double& p: instance.jobSize){
        cout << p << " ";
    }
    cout << endl;
    cout << "Machine speeds: ";
    for(const double& s: instance.speed){
        cout << s << " ";
    }
    cout << endl;
}

