import subprocess

def start_service(hostname, service_name):
    """
    Starts a service on a remote Windows machine using `sc`.
    
    :param hostname: The hostname or IP address of the remote machine.
    :param service_name: The name of the service to start.
    """
    cmd = ["sc", f"\\\\{hostname}", "start", service_name]
    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode == 0:
        print(f"Service '{service_name}' started successfully on {hostname}.")
    else:
        print(f"Failed to start service '{service_name}' on {hostname}. Error:\n{result.stderr}")


def stop_service(hostname, service_name):
    """
    Stops a service on a remote Windows machine using `sc`.
    
    :param hostname: The hostname or IP address of the remote machine.
    :param service_name: The name of the service to stop.
    """
    cmd = ["sc", f"\\\\{hostname}", "stop", service_name]
    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode == 0:
        print(f"Service '{service_name}' stopped successfully on {hostname}.")
    else:
        print(f"Failed to stop service '{service_name}' on {hostname}. Error:\n{result.stderr}")
