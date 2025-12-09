import glob
import os
import subprocess
import sys


def create_goal_files():
    """Step 1: Generate .trace.goal files from .trace files."""
    print("--- Step 1: Generating .trace.goal files ---")

    trace_files = glob.glob("*.trace")
    trace_files.sort()

    if not trace_files:
        print("No .trace files found in the current directory.")
        return []

    generated_files = []

    for trace_file in trace_files:
        # Extract the identifier (e.g., '01' from '01.trace')
        stem = trace_file.replace(".trace", "")

        # Define the output filename
        goal_filename = f"{trace_file}.goal"

        # Construct the content string
        content = f'Flag(FileOn("{stem}.replay.res")) & ("{trace_file}")'

        try:
            with open(goal_filename, "w") as f:
                f.write(content)
            print(f"  Created: {goal_filename}")
            generated_files.append(goal_filename)
        except IOError as e:
            print(f"  Error writing {goal_filename}: {e}")

    return generated_files

def gen_replays_and_consolidate():
    """Step 2: Run krt on goal files and consolidate output."""
    print("\n--- Step 2: Running krt and creating all_replays.txt ---")

    goal_files = glob.glob("*.trace.goal")
    goal_files.sort()

    if not goal_files:
        print("No goal files to process.")
        return

    all_replays_filename = "all_replays.txt"

    # Open the master file to consolidate everything
    with open(all_replays_filename, "w") as all_outfile:

        for goal_file in goal_files:
            replay_file = goal_file.replace(".goal", ".replay")
            command = ["krt", "-b", "REPLAY.kin", goal_file]

            print(f"  Running: {' '.join(command)} > {replay_file}")

            try:
                # 1. Run the command and save to individual file
                with open(replay_file, "w") as outfile:
                    result = subprocess.run(
                        command,
                        stdout=outfile,
                        stderr=subprocess.PIPE,
                        text=True
                    )

                if result.returncode != 0:
                    print(f"    -> Failed (Code {result.returncode})")
                    print(f"    -> Error output:\n{result.stderr}")
                else:
                    # 2. If successful, append content to master file
                    try:
                        with open(replay_file, "r") as single_infile:
                            content = single_infile.read()

                        all_outfile.write(f"=== {replay_file} ===\n")
                        all_outfile.write(content)
                        all_outfile.write("\n")

                    except IOError as e:
                        print(f"    -> Error appending to master file: {e}")

            except FileNotFoundError:
                print("    -> Error: 'krt' executable not found. Check your PATH.")
                sys.exit(1)
            except IOError as e:
                print(f"    -> File I/O Error: {e}")

    print(f"  Combined output saved to '{all_replays_filename}'")

def cleanup_files():
    """Step 3: Remove intermediate .trace.goal and .replay.res files."""
    print("\n--- Step 3: Cleaning up intermediate files ---")

    # List patterns to delete
    patterns = ["*.trace.goal", "*.replay.res"]
    files_to_remove = []

    for pattern in patterns:
        files_to_remove.extend(glob.glob(pattern))

    if not files_to_remove:
        print("  Nothing to clean up.")
        return

    count = 0
    for f in files_to_remove:
        try:
            os.remove(f)
            count += 1
        except OSError as e:
            print(f"  Error deleting {f}: {e}")

    print(f"  Removed {count} intermediate files ({', '.join(patterns)}).")

def main():
    create_goal_files()
    gen_replays_and_consolidate()
    cleanup_files()
    print("\nWorkflow complete.")

if __name__ == "__main__":
    main()
