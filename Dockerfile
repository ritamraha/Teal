# Use a base image (e.g., Ubuntu)
FROM ubuntu:latest

# Prevent interactive prompts during package installations
ENV DEBIAN_FRONTEND=noninteractive

# Update the package list and install essential packages
RUN apt-get update && apt-get install -y \
    software-properties-common \
    && rm -rf /var/lib/apt/lists/*

# Add the deadsnakes PPA to get Python 3.9
RUN add-apt-repository ppa:deadsnakes/ppa

# Update the package list again and install Python 3.9 and pip
RUN apt-get update && apt-get install -y \
    python3.9 \
    python3.9-distutils \
    python3-pip

# Set the Python 3.9 binary as the default
RUN update-alternatives --install /usr/bin/python3 python3 /usr/bin/python3.9 1

# Verify Python and pip installation
RUN python3 --version
RUN pip3 --version

# Create a working directory (optional)
WORKDIR /app

# Copy the requirements.txt file into the container
COPY requirements.txt .

# Install Python packages from requirements.txt
RUN pip3 install -r requirements.txt

# ... (the rest of your Dockerfile)