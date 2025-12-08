import glob
import subprocess
import sys

def gen_replays():
    # 1. Find all files ending in .trace.goal
    goal_files = glob.glob("*.trace.goal")
    goal_files.sort()

    if not goal_files:
        print("No .trace.goal files found in the current directory.")
        return

    print(f"Found {len(goal_files)} goal files. Processing...\n")

    for goal_file in goal_files:
        # Determine the output filename: 
        # "01.trace.goal" -> "01.trace.replay"
        replay_file = goal_file.replace(".goal", ".replay")
        
        # The command to run
        command = ["krt", "-b", "REPLAY.kin", goal_file]
        
        print(f"Running: {' '.join(command)} > {replay_file}")

        try:
            # Open the output file in write mode
            with open(replay_file, "w") as outfile:
                # Run the command, redirecting stdout to the file
                # stderr is captured so we can print it if there's an error
                result = subprocess.run(
                    command, 
                    stdout=outfile, 
                    stderr=subprocess.PIPE, 
                    text=True
                )

            # Check if the command was successful
            if result.returncode != 0:
                print(f"  -> Failed (Code {result.returncode})")
                print(f"  -> Error output:\n{result.stderr}")
            else:
                # Optional: If you want to see stderr even on success (warnings), uncomment below
                # if result.stderr: print(f"  -> Warnings: {result.stderr}")
                pass

        except FileNotFoundError:
            print("  -> Error: 'krt' executable not found. Check your PATH.")
            sys.exit(1)
        except IOError as e:
            print(f"  -> File I/O Error: {e}")

if __name__ == "__main__":
    gen_replays()
