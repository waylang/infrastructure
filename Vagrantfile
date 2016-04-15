require 'ostruct'
require 'pathname'

Vagrant.configure('2') do |config|
  if Vagrant.has_plugin?('vagrant-cachier')
    config.cache.scope = :box # http://fgrehm.viewdocs.io/vagrant-cachier/usage/
  end

  config.vm.box = 'ubuntu/trusty64'
  config.vm.hostname = 'metatheory'
  config.ssh.forward_agent = true

  config.vm.network 'forwarded_port', guest: 80, host: 80

  %w(vmware_fusion vmware_workstation).each do |vmware|
    config.vm.provider vmware do |provider, override|
      provider.name = 'metatheory'
      override.vm.box = 'netsensia/ubuntu-trusty64'
    end
  end

  config.vm.provider 'virtualbox' do |provider, _override|
    provider.name = 'metatheory'
  end

  if File.exist? "#{ENV['HOME']}/.gitconfig"
    config.vm.provision :file, source: '~/.gitconfig', destination: '.gitconfig'
  end

  config.vm.provision :shell, inline: %(
which chef || wget -qO - https://www.chef.io/chef/install.sh | bash -s -- -P chefdk
berks vendor -b /vagrant/Berksfile /tmp/vagrant-chef/cookbooks
)

  config.vm.provision :chef_solo do |chef_solo|
    chef_solo.install = false
    chef_solo.binary_path = '/opt/chefdk/bin'
    chef_solo.add_recipe 'metatheory::vagrant'
  end

  # If Vagrantfile.custom exists, read and eval it in this context
  vagrant_custom = Pathname.new(__FILE__).parent + 'Vagrantfile.custom'
  if File.exist?(vagrant_custom)
    OpenStruct.new(config: config).instance_eval File.read(vagrant_custom)
  end
end
