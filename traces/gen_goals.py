import glob


def create_goal_files():
    # Find all files ending in .trace in the current directory
    trace_files = glob.glob("*.trace")

    # Sort them to process in order (optional, but looks nicer in output)
    trace_files.sort()

    if not trace_files:
        print("No .trace files found in the current directory.")
        return

    for trace_file in trace_files:
        # Extract the identifier 'i' (e.g., '01' from '01.trace')
        # We assume the stem is everything before the last .trace
        stem = trace_file.replace(".trace", "")

        # Define the output filename
        goal_filename = f"{trace_file}.goal"

        # Construct the content string
        # Flag(FileOn("01.replay.res")) & ("01.trace")
        content = f'Flag(FileOn("{stem}.replay.res")) & ("{trace_file}")'

        # Write to the file
        try:
            with open(goal_filename, "w") as f:
                f.write(content)
            print(f"Created: {goal_filename}")
        except IOError as e:
            print(f"Error writing {goal_filename}: {e}")

if __name__ == "__main__":
    create_goal_files()
