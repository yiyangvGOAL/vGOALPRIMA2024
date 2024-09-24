import TS_Generation_V2 as TG
import time
import Interface_NuSMV_V2 as Interface_NuSMV
import Interface_Storm_V2 as Interface_Storm
import subprocess
import numpy as np
import matplotlib.pyplot as plt
import sys
start = time.time()

def Run_vGOAL(action_probability,p):
    knowledge_base =["forall p. dropped(p) implies delivered(p)",
                     "exists p. at(6) implies located(charging)",
                     "exists p. at(7) implies located(charging)",
                     "exists p. at(8) implies located(charging)",
                     "battery(1) implies safe1",
                     "battery(2) implies safe1",
                     "exists p. at(p) and not at(9) implies safe2",
                     # Error implication
                     "E3 implies nonfatal",
                     "E1 implies nonfatal",
                     "E2 implies nonfatal",
                     "E4 implies fatal",
                     "equal(1,1)",
                     "equal(2,2)",
                     "equal(3,3)",
                     "equal(4,4)",
                     "equal(5,5)",
                     "equal(6,6)",
                     "equal(7,7)",
                     "equal(8,8)",
                     "equal(9,9)",
                     "equal(10,10)",
                     "equal(A1,A1)",
                     "equal(A2,A2)",
                     "equal(A3,A3)",
                     "equal(_,_)",
                     "equal(charging,charging)"]
    constraints_of_action_generation = [
        # Ensure the decision-making module will not generate decisions before the revision of goals and beliefs when encountering errors.
        "forall p. at(p) and fatal implies M(p)",
        "a-goal-holding and not holding and docked(3) and not nonfatal and not E1 and not fatal implies A",
        "a-goal-holding and not holding and docked(4) and not nonfatal and not E1 and not fatal implies A",
        # From P4 to P2
        "a-goal-at(2) and docked(4) and holding and assigned(2) and not E3 and not fatal implies B(4)",
        # From P3 to P2
        "a-goal-at(2) and docked(3) and holding and assigned(2) and not E3 and not fatal implies B(3)",
        #Request location permission for P2.
        "exists x. a-goal-at(2) and docked(x) and holding and not fatal implies S(2)",
        # AMR goes from P1 to P3 or P4, from P6, P7, P8 to P3 or P4, from P2 to P5, from P5 to P6, P7,P8
        "forall p. a-goal-at(p) and not holding and not equal(p,2) and assigned(p) and not fatal implies C(p)",
        "exists p. a-goal-at(p) and holding and holding_error and assigned(p) and not fatal implies C(p)",
        "exists p. a-goal-at(p) and holding and docking_error and assigned(p) and not fatal implies C(p)",
        "exists p. a-goal-at(p) and docking_error and assigend(p) and not fatal implies C(p)",
        "forall p. a-goal-at(p) and not holding and not equal(p,2) and not fatal implies S(p)",
        "exists p. a-goal-at(p) and holding and holding_error and not fatal implies S(p)",
        "a-goal-at(5) and docking_error and at(2) and not assigned(5) and not fatal implies S(5)",
        "a-goal-at(5) and docking_error and at(3) and not assigned(5) and not fatal implies S(5)",
        "a-goal-at(5) and docking_error and at(4) and not assigned(5) and not fatal implies S(5)",
        # To be changed
        "forall p. a-goal-delivered(p) and at(p) and docked(p) and holding and not E2 and not fatal implies D(p)",

        "forall p. a-goal-battery(2) and assigned(p) and battery(1) and docked(p) and not fatal implies E(p)",
        "a-goal-located(charging) and at(5) and not fatal implies F",
        "exists x,y. reserved(x,y) implies G"
    ]
    enableness_of_actions = [
        "A implies pickup",
        "A implies pickup_fail",
        # from P3,P4 to P2
        "forall x. B(x) implies move3(x,2)",
        "forall x. B(x) implies move3_fail(x,2)",
        "forall x. B(x) implies move3_fail2(x,2)",
        # from P2,P3,P4,P6,P7,P8 to P5
        "forall y. C(5) and at(y) and docked(y) and not equal(y,1) implies move4(y,5)",
        "forall y. C(5) and at(y) and docked(y) and not equal(y,1) implies move4_fail(y,5)",
        # from P2,P3,P4,P6,P7,P8 to P5 Docking Error handling
        "forall p. C(p) and at(2) and docking_error implies move1(2,p)",
        "forall p. C(p) and at(2) and docking_error implies move1_fail(2,p)",
        "forall p. C(p) and at(3) and docking_error implies move1(3,p)",
        "forall p. C(p) and at(3) and docking_error implies move1_fail(3,p)",
        "forall p. C(p) and at(4) and docking_error implies move1(4,p)",
        "forall p. C(p) and at(4) and docking_error implies move1_fail(4,p)",
        # from P2,P3,P4,P6,P7,P8 to P2,P3,P4,P6,P7,P8
        "forall p,y. C(p) and at(y) and not equal(y,1) and not equal(y,5) and not equal(p,1) and not equal(p,5) implies move3(y,p)",
        "forall p,y. C(p) and at(y) and not equal(y,1) and not equal(y,5) and not equal(p,1) and not equal(p,5) implies move3_fail(y,p)",
        "forall y. C(2) and at(y) and not equal(y,1) and not equal(y,5) and not E3 implies move3_fail2(y,2)",
        "forall y. C(3) and at(y) and not equal(y,1) and not equal(y,5) and not E3 implies move3_fail2(y,3)",
        "forall y. C(4) and at(y) and not equal(y,1) and not equal(y,5) and not E3 implies move3_fail2(y,4)",

        # from P5 to P6,P7,P8
        "forall p. C(p) and at(5) and implies move2(5,p)",
        "forall p. C(p) and at(5) and implies move2_fail(5,p)",
        "forall p. C(p) and at(5) and implies move2_fail2(5,p)",
        "exists p. D(p) implies dropoff(p)",
        "exists p. D(p) implies dropoff_fail(p)",
        "forall p. E(p) implies charging(p)",
        "forall p. E(p) implies charging_fail(p)",
    ]
    sent_message_update = [
        "F implies send!(C) idle(_)",
        "G implies send?(allother) released(_)",
        "forall p. S(p) implies send!(C) idle(p)",
        "forall y. M(y) implies send!(C) at(y)"
    ]

    event_processing = [
        # Fatal Error handling
        "E4 implies insert charging_error",
        "fatal implies drop allgoals",
        "fatal implies delete all",
        "located(charging) and pick_error implies delete pick_error",
        #Fix error rules for the static verification
        "exists x. holding and located(charging) and holding_error implies delete holding",
        "located(charging) and holding_error implies delete holding_error",
        "exists x. holding and located(charging) and docking_error implies delete holding",
        "located(charging) and docking_error implies delete docking_error",
        "forall p. at(5) and dropped(p) implies delete dropped(p)",
        # Nonfatal Error handling
        "nonfatal and not located(charging) implies drop all",
        "nonfatal and not located(charging) implies adopt located(charging)",
        "nonfatal and not located(charging) implies adopt at(5)",
        "E3 implies insert docking_error",
        "E1 implies insert pick_error",
        "E2 implies insert holding_error",
        #"nonfatal and not goal_change implies insert goal_change",
        "nonfatal and E3 implies delete E3",
        "nonfatal and E1 implies delete E1",
        "nonfatal and E2 implies delete E2",
        #Release location permission for the fatal agent
        "forall z. exists x,y. sent!(x) at(y) and reserved(x,z) implies insert idle(z)",
        "forall x,z. exists y. sent!(x) at(y) and reserved(x,z) implies delete reserved(x,z)",
        # Normal event processing
        "forall x,z in D6 . exists y. sent!(x) idle(y) and idle(y) and not reserved(z,y) implies insert reserved(x,y)",
        "forall x. exists y. sent!(x) idle(y) and reserved(x,y) implies send:(x) assigned(y)",
        "forall y. exists x,z. sent!(x) idle(y) and reserved(z,y) and equal(x,z) implies delete idle(y)",
        "forall x,y. sent?(x) released(_) and released(y) implies send:(x) idle(y)",
        "forall y. exists x. sent?(x) released(_) and released(y) implies delete released(y)",
        "forall y. exists x. sent:(x) idle(y) implies insert idle(y)",
        "forall y. exists x. sent:(x) idle(y) implies delete reserved(x,y)",
        "forall x,z in D6 ,m in D4 . sent!(x) idle(_) and idle(6) and not reserved(z,6) and not reserved(x,m) implies insert reserved(x,6)",
        "forall x. sent!(x) idle(_) and idle(6) and reserved(x,6) implies send:(x) assigned(6)",
        "exists x. sent!(x) idle(_) and reserved(x,6) implies delete idle(6)",
        "forall x,z in D6 ,m in D4 . sent!(x) idle(_) and idle(7) and not reserved(z,7) and not reserved(x,m) implies insert reserved(x,7)",
        "forall x. sent!(x) idle(_) and idle(7) and reserved(x,7) implies send:(x) assigned(7)",
        "exists x. sent!(x) idle(_) and reserved(x,7) implies delete idle(7)",
        "forall x,z in D6 ,m in D4 . sent!(x) idle(_) and idle(8) and not reserved(z,8) and not reserved(x,m) implies insert reserved(x,8)",
        "forall x. sent!(x) idle(_) and idle(8) and reserved(x,8) implies send:(x) assigned(8)",
        "exists x. sent!(x) idle(_) and reserved(x,8) implies delete idle(8)",
        "forall y. exists x. sent:(x) assigned(y) implies insert assigned(y)",
        "forall p. exists s. a-goal-transport(s,p) implies adopt delivered(p)",
        "forall s. exists p. a-goal-transport(s,p) implies adopt at(s)",
        "forall p. exists s. a-goal-transport(s,p) implies adopt at(p)",
        "exists s,p. a-goal-delivered(p) implies adopt located(charging)",
        "exists p. a-goal-delivered(p) and not holding implies adopt holding",
        "exists p. a-goal-located(charging) and docked(2) and not holding implies adopt at(5)",
        "forall p. a-goal-located(charging) and at(5) and assigned(p) implies adopt at(p)",
        "forall s,p. a-goal-transport(s,p) implies drop transport(s,p)",
        "at(6) and battery(1) implies adopt battery(2)",
        "at(7) and battery(1) implies adopt battery(2)",
        "at(8) and battery(1) implies adopt battery(2)",
        "a-goal-at(6) and battery(1) and at(5) implies adopt battery(2)",
        "a-goal-at(7) and battery(1) and at(5) implies adopt battery(2)",
        "a-goal-at(8) and battery(1) and at(5) implies adopt battery(2)"
    ]

    action_specification = {
        "pickup": "pickup and not holding implies holding",
        "pickup_fail": "pickup_fail implies E1",
        "dropoff": "forall p. dropoff(p) and holding implies dropped(p) and not holding",
        "dropoff_fail": "dropoff_fail implies E2",
        # move2: from P5 to P6, P7, P8
        "move2": "forall x,y. move2(x,y) and at(x) implies at(y) and not at(x) and docked(y) and not assigned(x) and released(x)",
        "move2_fail": "exists x,y. move2_fail(x,y) implies E5",
        "move2_fail2": "exists x,y. move2_fail2(x,y) and at(x) implies E3 and at(y) and not at(x) and not assigned(x) and released(x)",
        # move3: from P2, P3, P4, P5, P6, P7, P8 to P2, P3, P4,  P6, P7, P8
        "move3": "forall x,y. move3(x,y) and at(x) and docked(x) implies at(y) and not at(x) and docked(y) and not docked(x) and not assigned(x) and released(x)",
        "move3_fail": "exists x,y. move3_fail(x,y) implies E5",
        "move3_fail2": "forall x,y. move3_fail2(x,y) and at(x) and docked(x) implies E3 and at(y) and not at(x) and not docked(x) and not assigned(x) and released(x)",
        # move4: from P2, P3, P4, P5, P6, P7, P8 to P5
        "move4": "forall x,y. move4(x,y) and at(x) and docked(x) implies at(y) and not at(x) and not docked(x) and not assigned(x) and released(x)",
        "move4_fail": "exists x,y. move4_fail(x,y) implies E5",
        # move1: from undocked P2, P3, P4, P5, P6, P7, P8  to P5
        "move1": "forall x,y. move1(x,y) and at(x) implies at(y) and not at(x) and not assigned(x) and released(x)",
        "move1_fail": "exists x,y. move1_fail(x,y) implies E5",
        "charging": "exists p. charging(p) and battery(1) implies battery(2) and not battery(1)",
        "charging_fail": "exists p. charging(p) and battery(1) implies E4"
    }
    domain = {"D1": ["2", "3", "4", "5", "6", "7", "8"], "D2": ["1", "2", "3", "4", "5", "6", "7", "8",  "9", "10"],
              "D3": ["1", "2","3", "4", "5", "6", "7", "8"], "D5": ["1", "2"],
              "D4":["6", "7", "8"],"D6": ["A1", "A2","A3"],"D61":["A1"]}
    constants = ["0", "1", "2","3", "4", "5", "6", "7", "8",  "9", "10","charging","allother", "all", '_',"A1","A2","A3","C","D"]

    belief_base1 = ["at(6)", "battery(1)", "docked(6)", "assigned(6)"]
    belief_base2 = ["at(7)", "battery(1)","docked(7)","assigned(7)"]
    belief_base3 = ["at(8)", "battery(1)","docked(8)","assigned(8)"]
    belief_base4 = ["idle(2)", "idle(3)", "idle(4)","idle(5)", "reserved(A1,6)", "reserved(A2,7)", "reserved(A3,8)"]

    goal_base1 = ['transport(3,2)']
    goal_base2 = ['transport(4,2)']
    goals1=[goal_base1,goal_base1,goal_base1,goal_base1,goal_base1,goal_base1,goal_base1,goal_base1,goal_base1,goal_base1]
    goals1 = [goal_base2, goal_base1, goal_base2, goal_base1, goal_base2, goal_base1, goal_base2, goal_base1,
              goal_base2, goal_base1]

    goals4 = []
    dummy_agents=["C"]
    safety_properties = {"A1": ["safe1", "safe2"], "A2": ["safe1","safe2"], "A3": ["safe1","safe2"]}
    prior_beliefs = []
    C = TG.Agent("C", belief_base4, goals4)
    flag=True
    goals1 = [goal_base1]#,goal_base2,goal_base1 ,goal_base2]#,goal_base2]#,goal_base1,goal_base2,goal_base1,goal_base2]#,goal_base2,goal_base1,goal_base1,goal_base1,goal_base2,goal_base1]
    goals2 = [goal_base2]#,goal_base2]#,goal_base1,goal_base2]#goal_base2,goal_base2,goal_base2]#,goal_base2]#,goal_base2]#,goal_base2]#,goal_base1]
    goals3 = [goal_base1]#,goal_base1]#,goal_base1]#,goal_base2]#,goal_base1]
    A1 = TG.Agent("A1", belief_base1, goals1)
    A2 = TG.Agent("A2", belief_base2, goals2)
    A3 = TG.Agent("A3", belief_base3, goals3)
    Agents = [A1,C]
    Error_Messages= ["E1", "E2", "E3", 'E4','E5']
    Fatal_Error_Messgaes = ['charging_error']
    System_Error_Messages = ['E5']
    fatal_properties = ['charging_error']
    crash_properties = ["charging_error",'System_Crash']

    generated_system = TG.system_generation(Agents, knowledge_base, constraints_of_action_generation,
                                            enableness_of_actions, action_specification, sent_message_update,
                                            event_processing, domain, constants, dummy_agents,prior_beliefs,Fatal_Error_Messgaes,System_Error_Messages)

    end1 = time.time()
    system=generated_system[0]
    transitions=generated_system[1]
    properties=generated_system[2]
    final_states=generated_system[-1]
    start2=time.time()
    safety_symbol_properties, fatal_properties, F_properties, system_error_properties, crash_properties, error_properties, error_type_properties=Interface_NuSMV.interface_generation(system, transitions, properties,safety_properties,fatal_properties,System_Error_Messages, crash_properties, final_states,Error_Messages)

    end2=time.time()
    start3 = time.time()

    Interface_Storm.interface_generation(system, transitions, properties,action_probability,constants)

    #Interface_Storm.property_file_generation2(crash_properties,error_properties)
    Interface_Storm.property_file_generation3(crash_properties, error_type_properties)
    def run_python_file(filename):
        result = subprocess.run(
            ['/opt/homebrew/bin/python3.9', filename], capture_output=True, text=True
        )
        return result.stdout

    # Generate the Python file
    filename = "PCTL.py"
    # Run the generated Python file and capture the output
    stdout = run_python_file(filename)

    O=stdout.split("\n")
    row=[p]
    for o in O:
        #print(o)
        if o!='':
            o1 = float(o)
            row.append(o1)

    end3 = time.time()
    f = open("Record01.txt", "w+")
    f.write("The time for transition system generation is :" + str(end1 - start) + '\n')
    f.write("The time for NuSMV encoding is :" + str(end2 - start2) + '\n')
    f.write("The time for PRISM encoding is :" + str(end3 - start3))
    f.close()
    f = open("System_Information01.txt", "w+")
    for key in system:
        f.write(key + '\n')
        for substate in system[key]:
            for key in substate:
                f.write(key + str(substate[key]) + '\n')
    for key in transitions:
        f.write(str(key) + '\n')
    for key in properties:
        f.write(key + '\n')
        for agent in properties[key]:
            f.write(agent + str(properties[key][agent]) + '\n')
    f.close()
    return row
def draw_graph(data,N):
    # Extract x and y values
    x = [row[0] for row in data]
    y_values = [list(col) for col in zip(*[row[1:] for row in data])]

    # Line styles and markers for differentiation
    line_styles = ['-', '--', '-.', ':', '-', '--', '-.','dashed']
    markers = ['o', 'x', 's', 'd', '^', 'v', '<','>']

    # Plot each line with distinct styles and markers
    for i, y in enumerate(y_values):
        style = line_styles[i % len(line_styles)]
        marker = markers[i % len(markers)]
        if i == 1:  # Specific condition to differentiate the second equal line
            plt.plot(x, y, linestyle='--', marker='x', color='r', label=f'Line {i + 1}')
        else:
            plt.plot(x, y, linestyle=style, marker=marker, label=f'Line {i + 1}')


    # Add a legend
    plt.legend()
    # Automatic layout adjustment
    plt.tight_layout()
    # Save the graph
    filename="E"+str(N+1)+".png"
    plt.savefig(filename)

    # Turn on interactive mode
    plt.ion()

    # Display the graph
    plt.show()

    # Wait for a short period before closing the window
    #
    # plt.pause(5)  # Adjust the time as needed

    # Close the figure
    plt.close()
#0.2, 0.2, 0.15, 0.01, 0.1
def probability_generation(p1, p2, p3, p4, p5):
    action_probability = {
        'pickup': 1-p1,
        'pickup_fail': p1,
        'dropoff': 1-p2,
        'dropoff_fail': p2,
        'move1': 1-p5,
        'move1_fail': p5,
        'move2': 1-p3-p5,
        'move2_fail': p5,
        'move2_fail2': p3,
        'move3': 1-p3-p5,
        'move3_fail': p5,
        'move3_fail2': p3,
        'move4': 1-p5,
        'move4_fail': p5,
        'charging': 1-p4,
        'charging_fail': p4,
    }

    return action_probability


def main():
    start = time.time()
    for N in range(0, 5):
        P = [0.2, 0.2, 0.1, 0.1, 0.15]
        if N==2:
            prob_list = np.arange(0.01, 1-P[4], 0.05).tolist()
        elif N==4:
            prob_list = np.arange(0.01, 1-P[2], 0.05).tolist()
        else:
            prob_list = np.arange(0.01, 1.01, 0.05).tolist()
            #prob_list = np.arange(0.01, 0.05, 0.05).tolist()
        data = []
        for p1 in prob_list:
            print(p1)
            P[N]=p1
            action_probability = probability_generation(P[0], P[1], P[2], P[3], P[4])
            row = Run_vGOAL(action_probability, p1)
            data.append(row)
        f = open("E"+str(N+1)+".txt", "w+")
        f.write("[\n")
        for item in data:
            f.write("%s,\n" % item)
        f.write("]\n")
        f.close()

        draw_graph(data,N)
    end = time.time()
    print("The time for the whole process is :" + str(end - start))
    f = open("Total_Time_Record.txt", "w+")
    f.write("The time for the whole process is :" + str(end - start) + '\n')
    f.close()
main()