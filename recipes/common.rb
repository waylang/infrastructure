include_recipe 'apt'

project_user = node['infrastructure']['project_user']
project_root = node['infrastructure']['project_root']

# Install git from PPA
apt_repository 'git-ppa' do
  uri 'http://ppa.launchpad.net/git-core/ppa/ubuntu'
  distribution node['lsb']['codename']
  components %w(main)
  key 'E1DF1F24'
  keyserver 'keyserver.ubuntu.com'
end

package 'bash-completion'
package 'curl'
package 'dstat'
package 'git'
package 'iftop'
package 'iotop'
package 'iperf'
package 'jq'
package 'lsof'
package 'man-db'
package 'mlocate'
package 'nano'
package 'strace'
package 'sysstat'
package 'unzip'
package 'wget'
package 'zip'

# Install our gem dependencies if any
execute 'bundle-install' do
  command "bundle install --gemfile=#{project_root}/Gemfile"
  user project_user
  only_if { File.exist? "#{project_root}/Gemfile" }
end
