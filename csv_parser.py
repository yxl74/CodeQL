import json
import csv
import sys
import subprocess
from collections import defaultdict

def run_codeql_query(query_path, output_bqrs):
    try:
        subprocess.run(['codeql', 'query', 'run', query_path, '--output=' + output_bqrs], check=True)
        print(f"CodeQL query executed successfully. Output written to {output_bqrs}")
    except subprocess.CalledProcessError as e:
        print(f"Error executing CodeQL query: {e}")
        sys.exit(1)

def convert_bqrs_to_csv(input_bqrs, output_csv):
    try:
        subprocess.run(['codeql', 'bqrs', 'decode', '--format=csv', input_bqrs, '--output=' + output_csv], check=True)
        print(f"BQRS file converted to CSV successfully. Output written to {output_csv}")
    except subprocess.CalledProcessError as e:
        print(f"Error converting BQRS to CSV: {e}")
        sys.exit(1)

def parse_csv_results(input_file, output_file):
    try:
        with open(input_file, 'r', newline='') as f:
            reader = csv.reader(f)
            # Read the header
            header = next(reader)
            # Create a mapping from your expected field names to the actual CSV column indices
            field_mapping = {
                'componentType': header.index('componentType') if 'componentType' in header else -1,
                'componentName': header.index('componentName') if 'componentName' in header else -1,
                'isExported': header.index('isExported') if 'isExported' in header else -1,
                'permissionNeeded': header.index('permissionNeeded') if 'permissionNeeded' in header else -1,
                'permissionLevel': header.index('permissionLevel') if 'permissionLevel' in header else -1
            }

            data = []
            for row in reader:
                item = {}
                for field, index in field_mapping.items():
                    if index != -1:
                        item[field] = row[index]
                    else:
                        item[field] = "N/A"  # or some default value
                data.append(item)

        # Generate summary statistics
        summary = generate_summary(data)

        # Combine data and summary
        result = {
            "components": data,
            "summary": summary
        }

        with open(output_file, 'w') as f:
            json.dump(result, f, indent=2)

        print(f"Successfully parsed CodeQL results. Output written to {output_file}")

    except FileNotFoundError:
        print(f"Error: Input file '{input_file}' not found.")
    except json.JSONDecodeError:
        print(f"Error: Failed to write JSON to '{output_file}'. Check disk space and permissions.")
    except Exception as e:
        print(f"An unexpected error occurred: {str(e)}")

def generate_summary(data):
    total_components = len(data)
    exported_components = sum(1 for item in data if item["isExported"].lower() == "true")
    permission_levels = defaultdict(int)
    component_types = defaultdict(int)
    permission_needed = defaultdict(int)

    for item in data:
        permission_levels[item["permissionLevel"]] += 1
        component_types[item["componentType"]] += 1
        permission_needed[item["permissionNeeded"]] += 1

    return {
        "totalComponents": total_components,
        "exportedComponents": exported_components,
        "permissionLevels": dict(permission_levels),
        "componentTypes": dict(component_types),
        "permissionNeeded": dict(permission_needed)
    }

if __name__ == "__main__":
    if len(sys.argv) != 4:
        print("Usage: python script_name.py <query_path> <bqrs_output> <json_output>")
        sys.exit(1)

    query_path = sys.argv[1]
    bqrs_output = sys.argv[2]
    json_output = sys.argv[3]

    # Step 1: Run CodeQL query
    run_codeql_query(query_path, bqrs_output)

    # Step 2: Convert BQRS to CSV
    csv_output = bqrs_output.rsplit('.', 1)[0] + '.csv'
    convert_bqrs_to_csv(bqrs_output, csv_output)

    # Step 3: Parse CSV and generate JSON
    parse_csv_results(csv_output, json_output)
