#
#	INSTAL stable
#	
#	This Dockerfile provides an image for INSTAL-stable
#
#	This is a multi-part file which installs the clingo dependency as a separate image
#	which is then used to build the instal-stable image
#
	


##### setting up clingo 


# using a base python image to install clingo
FROM python:3.5.3 AS clingo_5.1.0


# clingo version & release URL (incase things change)

ARG clingo_release_url=https://github.com/potassco/clingo/archive/refs/tags/v
ARG clingo_version=5.1.0


# resolving issues with Debian Jesse version, refer to link: 
# https://stackoverflow.com/questions/75836790/docker-packages-404-not-found-from-node8-jessie
RUN rm /etc/apt/sources.list
RUN echo "deb http://archive.debian.org/debian-security jessie/updates main" >> /etc/apt/sources.list.d/jessie.list
RUN echo "deb http://archive.debian.org/debian jessie main" >> /etc/apt/sources.list.d/jessie.list


# running updates and installing dependencies
RUN apt-get update && apt-get install -y --force-yes \
curl \
libpq-dev \
libstdc++6 \
libgcc-4.9-dev \
g++ \
gcc \
wget \
scons \ 
bison \
re2c


# Dowload clingo archive (tar.gz)
RUN curl -L ${clingo_release_url}${clingo_version}.tar.gz > clingo-${clingo_version}.tar.gz


# extract and build clingo
RUN  tar -xvzf clingo-${clingo_version}.tar.gz && cd clingo-${clingo_version} && scons --build-dir=release

# delete download
RUN rm clingo-${clingo_version}.tar.gz

# change ownership to instal (avoid using root)
#RUN useradd instal
#RUN chown -R instal ../clingo-${clingo_version}

# change user (avoid using root)
#USER instal 

# echo warning
CMD ["echo", "USAGE: to build INSTAL image upon"]



##### setting up instal-stable
# using previous stage (clingo) to build instal stable
FROM clingo_5.1.0 as instal_stable

# instal stable version
ARG instal_release_url=https://github.com/instsuite/instal-stable/archive/refs/tags/v1.0.0.tar.gz


# download INSTAL stable
RUN curl -L ${instal_release_url} > instal-stable.tar.gz


# extract
RUN  tar -xvzf instal-stable.tar.gz 

# delete download
RUN rm instal-stable.tar.gz

# copy launcher file across
COPY ./docker-launcher.py ../instal-stable-1.0.0

# copy clingo so file across
RUN cp /clingo-5.1.0/build/release/python/clingo.so ../instal-stable-1.0.0/instal/clingo.so

# install requirements
RUN pip install -r ../instal-stable-1.0.0/requirements.txt
WORKDIR ../instal-stable-1.0.0
RUN pip install . --force


# change ownership to instal (avoid using root)
RUN useradd instal
RUN chown -R instal ../instal-stable-1.0.0

# change user (avoid using root)
USER instal

# set entry point
ENTRYPOINT ["python3", "docker-launcher.py"]
