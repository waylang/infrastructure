project_name = node['infrastructure']['project_name']
project_user = node['infrastructure']['project_user']
project_root = node['infrastructure']['project_root']

# The canonical Vagrantfile
template "#{project_root}/Vagrantfile" do
  source 'vagrant/Vagrantfile.erb'
  variables name: project_name
end

# Create a version file if none exists
template "#{project_root}/version" do
  source 'vagrant/version.erb'
  not_if { File.exist?("#{project_root}/version") }
end

# Create a README.md if none exists
template "#{project_root}/README.md" do
  source 'vagrant/README.md.erb'
  variables name: project_name
  not_if { File.exist?("#{project_root}/README.md") }
end

# Create a .gemspec if none exists
template "#{project_root}/.gemspec" do
  source 'vagrant/.gemspec.erb'
  variables name: project_name
  not_if { File.exist?("#{project_root}/.gemspec") }
end

# Create a Gemfile if none exists
template "#{project_root}/Gemfile" do
  source 'vagrant/Gemfile.erb'
  not_if { File.exist?("#{project_root}/Gemfile") }
end

# Create a Berksfile if none exists
template "#{project_root}/Berksfile" do
  source 'vagrant/Berksfile.erb'
  not_if { File.exist?("#{project_root}/Berksfile") }
end

# A Rakefile
template "#{project_root}/Rakefile" do
  source 'vagrant/Rakefile.erb'
end

# Create a metadata.rb if none exists
template "#{project_root}/metadata.rb" do
  source 'vagrant/metadata.rb.erb'
  variables name: project_name
  not_if { File.exist?("#{project_root}/metadata.rb") }
end

# Create a chefignore if none exists
template "#{project_root}/chefignore" do
  source 'vagrant/chefignore.erb'
  not_if { File.exist?("#{project_root}/chefignore") }
end

# Create a .gitignore if none exists
template "#{project_root}/.gitignore" do
  source 'vagrant/.gitignore.erb'
  not_if { File.exist? "#{project_root}/.gitignore" }
end

# Create a .rspec
file "#{project_root}/.rspec" do
  content "--color --format documentation\n"
end

# Rubocop options
template "#{project_root}/.rubocop.yml" do
  source 'vagrant/.rubocop.yml.erb'
end

# Editor config
template "#{project_root}/.editorconfig" do
  source 'vagrant/.editorconfig.erb'
end

# Sublime Text project
template "#{project_root}/.sublime-project" do
  source 'vagrant/.sublime-project.erb'
  not_if { File.exist? "#{project_root}/.sublime-project" }
end

directory "#{project_root}/recipes" do
  owner project_user
  group project_user
end

# Create a recipes/vagrant.rb if none exists
template "#{project_root}/recipes/vagrant.rb" do
  source 'vagrant/recipes/vagrant.rb.erb'
  not_if { File.exist? "#{project_root}/recipes/vagrant.rb" }
end

directory "#{project_root}/spec" do
  owner project_user
  group project_user
end

# Create a spec/vagrant_spec.rb if none exists
template "#{project_root}/spec/vagrant_spec.rb" do
  source 'vagrant/spec/vagrant_spec.rb.erb'
  variables name: project_name
  not_if { File.exist? "#{project_root}/spec/vagrant_spec.rb" }
end

# Create a spec/spec_helper.rb if none exists
template "#{project_root}/spec/spec_helper.rb" do
  source 'vagrant/spec/spec_helper.rb.erb'
  not_if { File.exist? "#{project_root}/spec/spec_helper.rb" }
end

# Color shell prompts
execute "sed -i 's|#force_color|force_color|' /home/vagrant/.bashrc"

# Make a symlink named after the host to /vagrant
link "/home/vagrant/#{project_name}" do
  to project_root
  not_if { "/home/vagrant/#{project_name}" == project_root }
end

# Create a ~/.irbrc
template '/home/vagrant/.irbrc' do
  source 'home/vagrant/.irbrc.erb'
end

# Appropriate chefdk to be our general ruby
template '/etc/profile.d/chefdk.sh' do
  source 'etc/profile.d/chefdk.sh.erb'
end

include_recipe 'infrastructure::common'

# Run the serverspec suite enforcing that client-controlled files are up to date
execute 'rspec-project-spec' do
  cookbook_path = Pathname.new(__FILE__).parent.parent.to_s
  command "rspec --format documentation #{cookbook_path}/spec/project_spec.rb"
  cwd project_root
end
